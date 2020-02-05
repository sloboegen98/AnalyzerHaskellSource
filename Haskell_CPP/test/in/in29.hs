-- Даны типовые аннотации функций. Попытайтесь догадаться, что они делают,
-- дайте разумные имена и напишите их рекурсивные реализации (если вы
-- можете предложить несколько вариантов, реализуйте все):
-- 1) [a] -> Int -> a

index :: [a] -> Int -> a 
index [] _ = error "Index too large."
index (x:xs) n
	|n < 0 = error "Negative index"
	|n == 0 = x
	|otherwise = index xs (n-1)

-- 2) Eq a => [a] -> a -> Bool
elt :: Eq a => [a] -> a -> Bool
elt [] _ = False
elt (x:xs) a
	|x == a = True
	|otherwise = elt xs a

-- 3) [a] -> Int -> [a]
myTake :: [a] -> Int -> [a]
myTake _ 0 = []
myTake (x:xs) n = x : myTake xs (n-1)

-- 4) a -> Int -> [a]
nTimesByA :: a -> Int -> [a]
nTimesByA a 0 = []
nTimesByA a n = a : nTimesByA a (n-1)

-- 5) [a] -> [a] -> [a]
myConcat :: [a] -> [a] -> [a]
myConcat [] ys = ys
myConcat (x:xs) ys = x:myConcat xs ys

-- 6) (Eq a, Ord a) => [a] -> [[a]]
--Упорядочивает рядом стоящие по возрастанию и разбивает список на такие пары 
groupsByOrd :: (Eq a, Ord a) => [a] -> [[a]] 
groupsByOrd [] = [] 
groupsByOrd [x] = [x]:[] 
groupsByOrd (x:y:xs) = if x < y then [x,y] : groupsByOrd xs else [y,x] : groupsByOrd xs

-- 7) [a] -> [(Int, a)]

indexes :: [a] -> [(Int,a)]
indexes xs = go 0 xs
	where
	  go i (y:ys) = (i, y) : go (i+1) ys
	  go _ _ = []
	   
-- 8) Eq a => [a] -> [a]

onlyOneElt :: Eq a => [a] -> [a]
onlyOneElt [] = []
onlyOneElt (x:xs) = x : [y | y <- onlyOneElt xs, y /= x]

-- 9) (a -> Bool) -> [a] -> a

firstByPred :: (a -> Bool) -> [a] -> a
firstByPred f [] = error "Element not found"
firstByPred f (x:xs) =if f x then x else firstByPred f xs

-- 10) (a -> a) -> (a -> Bool) -> [a] -> [a]
--Создает элемент и, если удовлетворяет предикату, оставляет его в списке
myFunc :: (a -> a) -> (a -> Bool) -> [a] -> [a]
myFunc _ _ [] = []
myFunc f g (x:xs) = if g (f x) then f x: myFunc f g xs else myFunc f g xs