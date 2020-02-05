{-
  Задача 3 (10 баллов).
  Дан текстовый файл nets.txt, содержащий коды сетей класса A
  и наименования их владельцев.

  1) Разработайте алгебраический тип данных NetClass для хранения кодов.
  2) (2 б.) Напишите функцию, которая загружает данные из файла в список
     значений типа NetClass.
  3) (1 б.) Напишите функцию, которая по списку NetClass и коду
     возвращает наименование владельца.
  4) (4 б.) Напишите функцию, которая по списку NetClass и фрагменту
     названия владельца возвращает список подходящих владельцев и коды сетей.
  5) (3 б.) Напишите основную программу, которая загружает данные из файла
     анализирует параметры командной строки и в зависимости от них
     вызывает функцию из пунктов 3) или 4) и печатает результаты.
-}


import System.Environment
import Data.List.Split
import Data.List
import Data.Char

data NetClass = NC Int String deriving (Show)

loadFromFile :: String -> IO [NetClass]
loadFromFile path = do
  cont <- readFile path
  return $ map toNC $ splitOn "\n" cont
    where
      toNC s = (NC (read (head $ splitOn " " s)::Int) (unwords $ tail $ splitOn " " s))

takeOwner :: [NetClass] -> Int -> String
takeOwner lst code = getName $ head $ filter (\(NC c nm) -> c == code) lst
  where
    getName (NC c nm) = nm

getByPart :: [NetClass] -> String -> [NetClass]
getByPart lst sub = filter (\(NC c nm) -> isInfixOf (map toLower sub) (map toLower nm)) lst


argParse :: [String] -> IO ()
argParse (mode:rest) = case mode of
  "owner" -> do
    nc <- loadFromFile (head rest)
    print $ takeOwner nc (read (last rest)::Int)
  "part" -> do
    nc <- loadFromFile (head rest)
    print $ getByPart nc (last rest)
  otherwise -> do print "error"

main :: IO ()
main = do
  arg <- getArgs
  argParse arg

  print "end"
