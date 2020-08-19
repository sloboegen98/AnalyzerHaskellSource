#!/bin/python3

import json
import pymongo
from pymongo import MongoClient
from random import sample

class MuseumReport:
    exhibits_table = dict()
    mustown_table = dict()
    _max_length = 10

    def __init__(self, table, maxlen=10):
        self.exhibits_table = table
        self._max_length = maxlen

    def opt_get_town(self, museum):
        town = ""
        if 'города' in museum.lower():
            town = museum.split('города')[1].split()[0]
        elif 'городской' in museum.lower():
            town = museum.split('городской')[0].split()[-1]
        elif 'края' in museum.lower():
            town = museum.split('края', 1)[0].split()[-1]
        elif 'области' in museum.lower():
            town = museum.split('области')[0].split()[-1]

        return town

    def group_by_city(self):
        result_table = []
        for musexh in self.mustown_table.values():
            for mus, exh in musexh.items():
                result_table.append((mus, exh[:200]))

        if len(result_table) < 4:
            randmus = sample(self.exhibits_table.keys(), 3)
            for rk in randmus:
                result_table.append((rk, self.exhibits_table[rk]))

        return result_table[:self._max_length]

    def get_route(self):
        route = ""
        route_table = self.musfilter()

        for museum, exhibits in route_table:
            route += ("В музее " + museum + " Вы можете увидеть:\n")
            for exhibit in exhibits:
                route += ('- ' + exhibit + '\n')
            route += '\n'

        return route

    def musfilter(self):
        table_size = len(self.exhibits_table.keys())

        if table_size <= 3:
            return self.exhibits_table
        
        town = ""

        # Create dict by town, museums and exhibit
        for museum in self.exhibits_table.keys():
            town = self.opt_get_town(museum)
            cuttown = town[:4]

            if (cuttown != ""):
                if cuttown in self.mustown_table.keys():
                    continue
                else:
                    self.mustown_table.setdefault(cuttown, dict())
                    for m, e in self.exhibits_table.items():
                        if cuttown in m:
                            self.mustown_table[cuttown].setdefault(m, [])
                            self.mustown_table[cuttown][m].extend(e)
        
        # type of revelance_table is list
        # that helps save order
        relevance_table = self.group_by_city()

        return relevance_table


class MuseumsSearcher:
    exhibits = dict()
    collection = pymongo.collection.Collection
    person = ""

    def __init__(self):
        db = MongoClient().gc
        self.collection = db.subj

    def add_new_exhibit(self, data, name):
        musname = data['museum']['name']
        self.exhibits.setdefault(musname, [])
        self.exhibits[musname].append(name)

    def read_name(self):
        print('Введите имя человека, про которого вы хотете узнать: ')
        return (str(input())).replace('ё', 'е')

    def process_row(self, row):
            data = row['data']
            name = data['name'].replace('ё', 'е')
            data.setdefault('description', "")
            description = data['description'].replace('ё', 'е')

            # search better wihout end of the word
            pn = self.person.lower()[:-1] in name.lower()
            pd = description.lower().count(self.person.lower()) >= 2
            
            if pn or pd:
                self.add_new_exhibit(data, name)

    def print_results(self):
        for exhibit, museum in self.exhibits.items():
            print(exhibit, museum)

    def create_museums_list(self):
        self.person = self.read_name()
        for row in self.collection.find():
            self.process_row(row)

        return self.exhibits


def do_museum_route():
    ms = MuseumsSearcher().create_museums_list()
    mr = MuseumReport(ms)
    return mr.get_route()

route = do_museum_route()
print(route)
