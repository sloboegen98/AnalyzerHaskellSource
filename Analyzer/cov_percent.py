#!/bin/python3

from collections import defaultdict
from collections import Counter
import sys


table = open(sys.argv[1], 'r')
file_supp_ext = open(sys.argv[2], 'r')

ext_in_package = defaultdict(set)
supported_ext = set()
will_be_parsed_pull = Counter()
will_be_parsed_single = Counter()

# For each package add set of used extension
for line in table:
    line.rstrip()
    extension, package = line.split()
    ext_in_package[package].add(extension)

# Create a set of supported extension
for line in file_supp_ext:
    line.rstrip()
    xs = line.split()
    if xs[-1] == '+':
        ename = xs[0]
        # print(ename)
        supported_ext.add(ename)

# Calculate count of packages, which can be parsed
# Fill Counter: set unsupported extension -> Count of new packages, which will be parsed 
cnt_support = 0
for package in ext_in_package.keys():
    unsupported = ext_in_package[package].difference(supported_ext)

    if len(unsupported) == 0:
        cnt_support += 1
    else:
        will_be_parsed_pull[frozenset(unsupported)] += 1
        if (len(unsupported) <= 2):
            will_be_parsed_single[frozenset(unsupported)] += 1

print("Can parsed: " + str(cnt_support))
print("Count packages: " + str(len(ext_in_package.keys())))
cov_percent = (cnt_support) / (len(ext_in_package.keys())) * 100
print("Currnet per extension coverege: " + str(cov_percent))

print()

top_ext_pull = will_be_parsed_pull.most_common(20)
print(top_ext_pull)

print()

top_ext_single = will_be_parsed_single.most_common(20)
print(top_ext_single)