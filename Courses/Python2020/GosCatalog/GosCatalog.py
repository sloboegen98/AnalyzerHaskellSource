#!/bin/python3

import json
import pymongo
from pymongo import MongoClient
from zipfile import ZipFile
from sys import exit
from random import sample

client = MongoClient()
db = client.gc
collection = db.subj
collection.drop()

for_insert = []

with ZipFile('data-4-structure-3.json.zip') as myzip:
    for name in myzip.namelist():
        with myzip.open(name) as myfile:
            print(name)
            data = json.loads(myfile.read().decode('utf8'))
            for_insert.extend(sample(data, 10))


resp = collection.create_index([ ('_id', 1), ('name', 1) ])

print("Inserting to mongodb...")

try:
    collection.insert_many(for_insert)
except KeyboardInterrupt:
    print('Sorry!')
    exit(1)

print("Successfully inserted")
