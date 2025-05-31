import os
import re
import json
import time
import random
import requests
from loguru import logger
import execjs
import ddddocr

# 初始化
ocr = ddddocr.DdddOcr(det=False, ocr=False, show_ad=False)
session = requests.session()

# 常量
CAPTCHA_ID = '54088bb07d2df3c46b79f80300b0abbe'
IMG_DIR = './image'

os.makedirs(IMG_DIR, exist_ok=True)  # 确保图片目录存在

def generate_uuid():
    chars = 'xxxxxxxx-xxxx-4xxx-yxxx-xxxxxxxxxxxx'
    return ''.join(f'{random.randint(0, 15):x}' if c == 'x' else
                   f'{(random.randint(0, 15) & 0x3 | 0x8):x}' if c == 'y' else c
                   for c in chars)

def load_first():
    headers = {
        'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/137.0.0.0 Safari/537.36',
        'Referer': 'https://gt4.geetest.com/',
    }
    params = {
        'callback': 'geetest_' + str(int(time.time() * 1000)),
        'captcha_id': CAPTCHA_ID,
        'challenge': generate_uuid(),
        'client_type': 'web',
        'risk_type': 'slide',
        'lang': 'zh',
    }

    try:
        response = session.get('https://gcaptcha4.geetest.com/load', params=params, headers=headers)
        json_str = re.sub(r'^geetest_\d+\(|\);?$', '', response.text)
        data = json.loads(json_str)['data']
        result = {
            "process_token": data["process_token"],
            "payload": data["payload"],
            "slice": data["slice"],
            "bg": data["bg"],
            "lot_number": data["lot_number"]
        }
        logger.info(f"load_first result: {result}")
        return result
    except Exception as e:
        logger.error(f"[load_first] 加载失败: {e}")
        raise

def save_png(slice_path, bg_path):
    base_url = "https://static.geetest.com/"
    headers = {
        "referer": "https://www.gate.io/",
        "user-agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64)",
    }

    for name, path in {"slice": slice_path, "bg": bg_path}.items():
        try:
            url = base_url + path
            response = session.get(url, headers=headers)
            if response.status_code == 200:
                file_path = os.path.join(IMG_DIR, f"{name}.png")
                with open(file_path, 'wb') as f:
                    f.write(response.content)
                logger.info(f"图片保存成功: {file_path}")
            else:
                logger.warning(f"图片下载失败 [{name}]，状态码：{response.status_code}")
        except Exception as e:
            logger.error(f"[save_png] 下载图片 {name} 失败: {e}")

def get_distance():
    try:
        with open(os.path.join(IMG_DIR, 'slice.png'), 'rb') as f1, \
             open(os.path.join(IMG_DIR, 'bg.png'), 'rb') as f2:
            target = f1.read()
            background = f2.read()
        result = ocr.slide_match(target, background, simple_target=True)
        logger.info(f"识别偏移量: {result['target'][0]}")
        return result['target'][0]
    except Exception as e:
        logger.error(f"[get_distance] 获取偏移量失败: {e}")
        raise

def get_w(setLeft, lot_number, captcha_id):
    try:
        with open('纯算.js', 'r', encoding='utf-8') as f:
            js_code = f.read()
        w = execjs.compile(js_code).call('get_w', setLeft, lot_number, captcha_id)
        return w
    except Exception as e:
        logger.error(f"[get_w] JS执行失败: {e}")
        raise

def verify(lot_number, payload, process_token, w):
    headers = {
        'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64)',
        'Referer': 'https://gt4.geetest.com/',
    }

    params = {
        'callback': 'geetest_' + str(int(time.time() * 1000)),
        'captcha_id': CAPTCHA_ID,
        'client_type': 'web',
        'lot_number': lot_number,
        'risk_type': 'slide',
        'payload': payload,
        'process_token': process_token,
        'payload_protocol': '1',
        'pt': '1',
        'w': w,
    }

    try:
        response = session.get('https://gcaptcha4.geetest.com/verify', params=params, headers=headers)
        logger.success(f"验证结果: {response.text}")
    except Exception as e:
        logger.error(f"[verify] 验证请求失败: {e}")
        raise

if __name__ == '__main__':
    try:
        res = load_first()
        save_png(res['slice'], res['bg'])
        distance = get_distance()
        w = get_w(distance, res['lot_number'], CAPTCHA_ID)
        logger.info(f"生成 w 值: {w}")
        verify(res['lot_number'], res['payload'], res['process_token'], w)
    except Exception as e:
        logger.error(f"[主流程] 执行失败: {e}")
