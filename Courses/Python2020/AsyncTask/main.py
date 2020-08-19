from urllib.request import Request, urlopen
from bs4 import BeautifulSoup

from hashlib import md5

import time
import sys
import logging
import concurrent.futures
import asyncio


SUMMARY_TIME = 3600
PERIOD       = 60

def load_bs(url):
    HEADERS    = {'User-Agent': 'python'}
    try:
        response   = Request(url, headers=HEADERS)
        webContent = urlopen(response, timeout=60).read()
        return BeautifulSoup(webContent, 'lxml')
    except:
        logging.getLogger().error(f'connection with {url} failed...')


def load_news_portals():
    soup = load_bs('https://ua-ix.biz/ru/news/rossiya')
    portals = soup.findAll('span', attrs={'class':'ListSites__name'})

    return [f"http://{p.get_text()}" for p in portals] 


class PortalStatus:
    def __init__(self, news_portal : list):
        self.link        = news_portal
        self.portal_hash = 0
        self.uph         = 0
        self.text        = ""

    def calc_hash(self):
        soup = load_bs(self.link)

        for script in soup(['script', 'style']):
            script.extract()

        text = soup.get_text()
        self.text = self.filter_text(text)

        h = md5()
        h.update(self.text.encode('utf-8'))
        return h.hexdigest()

    def filter_text(self, text : str):
        must_remove = '\n\r\t1234567890 '
        for symbol in must_remove:
            text = text.replace(symbol, '')

        return text

    def refresh(self):
        cur_hash = self.calc_hash()
        if cur_hash != self.portal_hash:
            self.portal_hash = cur_hash
            self.uph += 1


class Portals:
    bad_portals = ['http://ytpo.ru', 'http://zhkhtv.ru', 'http://spravda.ru', 'http://novostik.com', 'http://novayagazeta.ru', 'http://smi2.ru', 'http://ria.ru']

    def __init__(self):
        self.urls = load_news_portals()
        self.urls = list(filter(lambda w : w not in self.bad_portals, self.urls))
        self.portals = [PortalStatus(portal) for portal in self.urls]

    def refresh(self):
        for portal in portals:
            portal.refresh()


class Report:
    def __init__(self, portals : Portals):
        self.report = self.create_report(portals.portals)

    def create_report(self, portals : list): 
        r = [(portal.uph, portal.link, portal.portal_hash) for portal in portals]
        return sorted(r, reverse=True)



def refresh_portlal(portal : PortalStatus):
    portal.refresh()
    log = logging.getLogger(f'{portal.link} {portal.portal_hash}')
    log.info('updated')
    return (portal.link, portal.portal_hash)


async def periodic_refresh(executor, portals):
    while True:
        executor.map(refresh_portlal, portals.portals)
        await asyncio.sleep(PERIOD)


if __name__ == '__main__':
    logging.basicConfig(
        level=logging.INFO,
        format='PID %(process)5s %(threadName)-25s %(name)-25s: %(message)s',
        stream=sys.stderr,
    )

    portals = Portals()
    th_number = len(portals.urls)
    executor = concurrent.futures.ThreadPoolExecutor(th_number)

    loop = asyncio.get_event_loop()
    task = loop.create_task(periodic_refresh(executor, portals))
    loop.call_later(SUMMARY_TIME, task.cancel)

    try:
        loop.run_until_complete(task)
    except asyncio.CancelledError:
        pass
    finally:
        loop.close()
        report = Report(portals)
        with open('report2.txt', 'w') as f:
            for uph, l, h in report.report:
                f.write(f'{l} {uph} {h}\n')
