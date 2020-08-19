from bs4 import BeautifulSoup
from urllib.request import Request, urlopen

import re


def _cut_caption(text):
    state = True
    result = ""
    for c in text:
        if state and c != '<':
            result += c 
        elif c == '<':
            state = False
        elif c == '>':
            state = True
    
    return result


class UrlExecutor:
    def __init__(self, url):
        self.soup    = self.load_url_content(url)
        self.content = list(zip(self._load_image_urls(), self._load_captions()))

    def load_url_content(self, url):
        USERAGENT = 'something'
        HEADERS   = {'User-Agent': USERAGENT}
        response  = Request(url, headers=HEADERS)
        webContent = urlopen(response).read()
        
        return BeautifulSoup(webContent, 'html.parser')

    def _load_image_urls(self):
        result = self.soup.findAll('div', attrs={'class':'thumbinner'})
        tmp = [item.find('img')['srcset'].split(',')[1] for item in result]
        # cut 1.5x and //
        tmp = list(map(lambda w: w[3:-3], tmp))
        return tmp

    def _load_captions(self):
        result = self.soup.findAll('div', class_='thumbinner')
        cs = []
        for item in result:
            item = item.find('div', attrs={'class' : 'thumbcaption'})
            cs.append(_cut_caption(str(item)))

        return cs
