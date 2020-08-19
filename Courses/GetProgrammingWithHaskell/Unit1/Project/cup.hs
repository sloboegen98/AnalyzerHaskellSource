cup ml = (\message -> message ml)
coffeeCup = cup 500

getMl aCup = aCup id

drink aCup mlDrank = if mlDiff >= 0
                     then cup mlDiff
                     else cup 0
    where 
        ml = getMl aCup
        mlDiff = ml - mlDrank

isEmpty aCup = getMl aCup == 0

afterManySips sips = foldl drink coffeeCup sips