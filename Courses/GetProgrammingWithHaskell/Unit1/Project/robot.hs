robot (name, attack, hp) = \message -> message (name, attack, hp)

name   (n, _, _) = n
attack (_, a, _) = a
hp     (_, _, h) = h

getName aRobot = aRobot name
getAttack aRobot = aRobot attack
getHp aRobot = aRobot hp

setName aRobot newName = aRobot (\(n, a, h) -> robot (newName, a, h))
setName aRobot newAttack = aRobot (\(n, a, h) -> robot (n, newAttack, h))
setName aRobot newHp = aRobot (\(n, a, h) -> robot (n, a, newHp))

printRobot aRobot = aRobot (\(n, a, h) -> n ++ ": attack: " ++ (show a) ++ ", hp: " ++ (show h))

damage aRobot attackDamage = aRobot (\(n, a, h) -> robot (n, a, h - attackDamage))

fight aRobot defender = damage defender attack
    where attack = if getHp aRobot > 0
                   then getAttack aRobot
                   else 0

killerRobot = robot ("killer", 25, 200)
friendRobot = robot ("robot", 10, 300)

rnd11 = fight killerRobot friendRobot
rnd12 = fight friendRobot killerRobot
rnd21 = fight killerRobot friendRobot
rnd22 = fight friendRobot killerRobot

getRobotsHp robotsList = map getHp robotsList

