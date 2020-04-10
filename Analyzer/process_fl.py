import sys
import re
from collections import Counter


def fill_implies():
    dimp = dict()
    dimp.setdefault('DeriveTraversable', [])
    dimp['DeriveTraversable'] = ['DeriveFunctor', 'DeriveFoldable']

    dimp.setdefault('DerivingVia', [])
    dimp['DerivingVia'] = ['DerivingStrategies']

    dimp.setdefault('FlexibleInstances', [])
    dimp['FlexibleInstances'] = ['TypeSynonymInstances']

    dimp.setdefault('FunctionalDependencies', [])
    dimp['FunctionalDependencies'] = ['MultiParamTypeClasses']

    dimp.setdefault('GADTs', [])
    dimp['GADTs'] = ['GADTSyntax', 'MonoLocalBinds']

    dimp.setdefault('ImplicitParams', [])
    dimp['ImplicitParams'] = ['FlexibleContexts', 'FlexibleInstances', 'TypeSynonymInstances']

    dimp.setdefault('ImpredicativeTypes', [])
    dimp['ImpredicativeTypes'] = ['RankNTypes']

    dimp.setdefault('IncoherentInstances', [])
    dimp['IncoherentInstances'] = ['OverlappingInstances']

    dimp.setdefault('PolyKinds', [])
    dimp['PolyKinds'] = ['KindSignatures']

    dimp.setdefault('RebindableSyntax', [])
    dimp['RebindableSyntax'] = ['NoImplicitPrelude']

    dimp.setdefault('RecordWildCards', [])
    dimp['RecordWildCards'] = ['DisambiguateRecordFields']

    dimp.setdefault('TypeFamilies', [])
    dimp['TypeFamilies'] = ['ExplicitNamespaces', 'KindSignatures', 'MonoLocalBinds']

    dimp.setdefault('TypeFamilyDependencies', [])
    dimp['TypeFamilyDependencies'] = ['TypeFamilies', 'ExplicitNamespaces', 'KindSignatures', 'MonoLocalBinds']

    dimp.setdefault('TypeOperators', [])
    dimp['TypeOperators'] = ['ExplicitNamespaces']

    return dimp


implies = fill_implies()

fl = open("full_list.txt", "r")

helplist = set()
for line in fl:
    ext, pack = line.split()
    ext.strip()
    pack.rstrip(' \n')
    helplist.add(ext + ' ' + pack)
    if ext in implies.keys():
        for implie in implies[ext]:
            helplist.add(implie + ' ' + pack)


extcounter = Counter()
for line in helplist:
    ext, pack = line.split()
    extcounter[ext] += 1

# diff with full_list.txt with implies
# 
# with open('extpack.txt', 'w') as f:
#     for ep in helplist:
#         e, p = ep.split()
#         f.write(e + ' ' + p + '\n')
#     f.close()

sortlist = extcounter.most_common()

with open('report.txt', 'w') as f:
    for ec in sortlist:
        f.write(str(ec[0]) + ' ' + str(ec[1]) + ' ' + '\n')
    f.close()