Automatically search for counter examples in small finite magmas.

Example:
```
python3 equational_theories/Generated/FinSearch/src/finsearch.py 4 168 2
```
This command searches for magmas over Fin 2, Fin 3 and Fin 4 aiming to find the theorem Equation168_not_implies_Equation2. It is possible to search for several "not implies" equations at once.

Example:
```
python3 insearch.py 2 1 4 3
```
This command searches for magmas over Fin 2 aiming to find the theorems Equation1_not_implies_Equation4 and Equation1_not_implies_Equation3

Example:
```
python3 insearch.py 5 467
```
This command searches for a magma over Fin 5 that satisfies equation 467.

Example:
```
python3 insearch.py 5 467 --search-all
```
This command searches for magmas over Fin 5 that satisfies equation 467 and provides counter examples to all other equations (if one exists)

# Method

A mixed integer linear program is set up that tries to determine the "truth table" for the magma. The problem is then solved using highs [https://highs.dev/]. The script relies on highspy being installed.
```
pip install highspy
```

Note: For best performance use the `latest` branch of highs.
