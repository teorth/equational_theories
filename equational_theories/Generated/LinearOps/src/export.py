import numpy as np
import os
import random

def parse_line(line):
    # Extract the list from the line using string manipulation
    try:
        if 'Proves' in line:
            return [x-1 for x in list(map(int, line.split('[')[1].split(']')[0].split(', ')))]
        else:
            return list(map(int, line.split(': ')[1].split(']')[0].split(', ')))
    except:
        print("Failed on", line)
        return []
    
def prune_rows(lines, matrix_size=4694):
    matrix = np.zeros((matrix_size, matrix_size), dtype=bool)
    matrix = np.load("/tmp/r.npy") != 8
    matrix[:] = 0
    print("ct", np.sum(matrix))

    random.shuffle(lines)
    keep = []
    for i,line in enumerate(lines):
        L = parse_line(line)
        L_array = np.array(L)
        
        # Create a boolean mask for elements not in L
        mask = np.ones(matrix_size, dtype=bool)
        mask[L_array] = False
        
        # Use advanced indexing to set values
        if np.any(matrix[L_array[:, None], mask] == 0):
            matrix[L_array[:, None], mask] = True
            keep.append(line)
                
    return matrix, keep

def trim(lines):
    """
    Compute an approximate covering set. Each table gives a set of refutations. 
    Repeatedly do the following:
      1. Randomly shuffle the table order
      2. Process the tables in linear order and drop those that don't add new rules
      3. Any time it doesn't improve things, increment a counter
      4. If we've made no progress 10 times, then call it "good enough"
    """
    print("Start with", len(lines))
    matrix, lines = prune_rows(lines)
    identity_count = 0
    while identity_count < 10:
        print("Current round", len(lines), np.sum(matrix))
        matrix2, lines2 = prune_rows(lines)
        assert np.all(matrix2 == matrix)
        if len(lines2) == len(lines):
            identity_count += 1
        lines = lines2
        #exit(0)
    return matrix, lines

print("Reading files...")
lines = []

for line in open("log").readlines():
    if "Loop" in line: continue
    if 'Variables' in line:
        vs = line[:-1]
    if 'Satisfied equations' not in line: continue
    lines.append(vs + " " + line)




print("Trimming...")
matrix, lines = trim(lines)

print("Covering set")
for line in lines:
    print(line)

template = """theorem MoreLinearInvariance{COUNT} : ∃ (G : Type) (_ : Magma G), Facts G {YES} {NOT} :=
  ⟨ZMod {PK}, {{ op := fun x y => {CONST1} * x + {CONST2} * y }}, by decide!⟩"""

#unsolved = {1486-1, 2126-1, 1076-1, 2531-1, 1133-1, 1167-1, 1659-1, 1661-1, 1485-1, 481-1, 3161-1, 1648-1, 1924-1, 2712-1, 1701-1, 1839-1, 511-1, 3116-1, 1443-1, 2093-1, 1692-1, 1895-1, 477-1, 1112-1, 2460-1, 3150-1, 854-1, 1110-1, 2497-1, 65-1, 73-1, 261-1, 274-1, 680-1, 707-1, 2940-1, 2947-1, 1523-1, 2132-1, 504-1, 1117-1, 1289-1, 1722-1, 1925-1, 2338-1, 2538-1, 3143-1, 3588-1, 3994-1, 713-1, 2856-1, 883-1, 917-1, 2710-1, 2744-1, 1086-1, 2541-1, 704-1, 1518-1, 2054-1, 2903-1, 3342-1, 4167-1, 118-1, 229-1, 1431-1, 1526-1, 2040-1, 2101-1, 115-1, 219-1, 476-1, 503-1, 907-1, 1447-1, 2056-1, 2700-1, 3069-1, 3076-1, 1519-1, 2128-1, 1630-1, 1633-1, 1681-1, 1833-1, 1884-1, 1958-1, 1113-1, 1515-1, 1729-1, 1898-1, 2038-1, 2534-1, 3549-1, 3917-1, 464-1, 706-1, 1276-1, 1437-1, 1441-1, 1516-1, 2037-1, 2070-1, 2091-1, 2291-1, 3103-1, 3308-1, 4158-1, 714-1, 1323-1, 2304-1, 2507-1, 63-1, 124-1, 206-1, 271-1, 1491-1, 2061-1, 467-1, 670-1, 677-1, 879-1, 906-1, 1728-1, 1841-1, 2504-1, 2647-1, 2650-1, 2866-1, 2910-1, 2937-1, 3140-1, 3352-1, 3475-1, 3545-1, 3555-1, 3888-1, 4164-1, 3862-1, 3862-1, 3456-1, 1832-1, 1629-1, 3253-1, 4065-1, 1426-1, 2035-1, 411-1, 3050-1, 817-1, 2644-1, 614-1, 1020-1, 2441-1, 2847-1, 4435-1, 1223-1, 2238-1, 3319-1, 3522-1, 3915-1, 4118-1, 8-1, 23-1, 47-1, 151-1, 255-1, 3457-1, 3877-1, 4268-1, 4587-1, 99-1, 203-1, 307-1, 359-1, 3511-1, 3955-1, 1657-1, 1860-1, 4380-1, 1519-1, 2128-1, 1055-1, 1429-1, 2124-1, 2452-1, 1701-1, 1839-1, 1630-1, 1633-1, 1681-1, 1833-1, 1884-1, 1958-1, 152-1, 166-1, 1096-1, 1427-1, 1481-1, 1483-1, 1492-1, 1634-1, 1656-1, 1660-1, 1668-1, 1721-1, 1837-1, 1851-1, 2051-1, 2087-1, 3460-1, 3520-1, 3524-1, 3527-1, 3659-1, 3897-1, 3972-1, 4006-1, 4040-1, 4314-1, 4315-1, 4606-1, 4615-1, 513-1, 1035-1, 1428-1, 2050-1, 2443-1, 3079-1, 3519-1, 3925-1, 4269-1, 4584-1, 1133-1, 1167-1, 1659-1, 1661-1, 1485-1, 477-1, 1112-1, 2460-1, 3150-1, 1523-1, 2132-1, 883-1, 917-1, 2710-1, 2744-1, 1113-1, 1515-1, 1729-1, 1898-1, 2038-1, 2534-1, 714-1, 1323-1, 2304-1, 2507-1, 3-1, 125-1, 167-1, 168-1, 222-1, 326-1, 375-1, 910-1, 1025-1, 1085-1, 1316-1, 1479-1, 1480-1, 1484-1, 1488-1, 1496-1, 1631-1, 1655-1, 1695-1, 1847-1, 1897-1, 2041-1, 2052-1, 2088-1, 2089-1, 2446-1, 2467-1, 2737-1, 3258-1, 3458-1, 3512-1, 3513-1, 3521-1, 3523-1, 3525-1, 3715-1, 3722-1, 3867-1, 3918-1, 3935-1, 3952-1, 3989-1, 3993-1, 4067-1, 4273-1, 4470-1, 4588-1, 1486-1, 2126-1, 481-1, 3161-1, 1648-1, 1924-1, 511-1, 3116-1, 1692-1, 1895-1, 65-1, 73-1, 261-1, 274-1, 680-1, 707-1, 2940-1, 2947-1, 504-1, 1117-1, 1289-1, 1722-1, 1925-1, 2338-1, 2538-1, 3143-1, 3588-1, 3994-1, 1086-1, 2541-1, 118-1, 229-1, 1431-1, 1526-1, 2040-1, 2101-1, 3549-1, 3917-1, 63-1, 124-1, 206-1, 271-1, 1491-1, 2061-1, 107-1, 205-1, 211-1, 413-1, 414-1, 416-1, 466-1, 473-1, 880-1, 1023-1, 1045-1, 1075-1, 1109-1, 1248-1, 1251-1, 1313-1, 1478-1, 1482-1, 1489-1, 1647-1, 1685-1, 1922-1, 2036-1, 2098-1, 2125-1, 2240-1, 2246-1, 2266-1, 2294-1, 2444-1, 2449-1, 2457-1, 2459-1, 2462-1, 2530-1, 2707-1, 3055-1, 3056-1, 3065-1, 3066-1, 3068-1, 3139-1, 3316-1, 3472-1, 3878-1, 4128-1, 4270-1, 4590-1}
unsolved = set(list(range(4694)))

solved = np.load("/tmp/r.npy") != 8
solved[:] = 0

fout = open("new.lean","w")
for count,line in list(enumerate(lines)):
    print("COUNT", count)
    PK, CONST1, CONST2 = map(int,line.split()[1:4])
    yes = list(map(int,line.split(": ")[1].split(", ")))
    no = list(set(unsolved)-set(yes))

    for _ in range(10):
        keepyes = []
        for x in yes:
            if not np.all(solved[x, no]):
                keepyes.append(x)
        yes = keepyes
    
        keepno = []
        for x in no:
            if not np.all(solved[yes, x]):
                keepno.append(x)
        no = keepno

    continue
    print("Intro", keepyes, keepno)
    if len(keepyes) == 0 or len(keepno) == 0:
        continue
    
    fout.write("@[equational_result]\n")
    fout.write(template.format(PK=PK, CONST1=CONST1, CONST2=CONST2, YES=[x+1 for x in yes], NOT=sorted([x+1 for x in no]), COUNT=count)+"\n\n")

    


#/eq/tables committed Current round 2204 13732880
#current set in .txt  Current round 515  13732566
#                     Current round 513  13737261

# 5x5: 14,187,469
#      14,472,076
# 22024116
