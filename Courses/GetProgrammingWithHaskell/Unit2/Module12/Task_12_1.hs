type FirstName  = String
type LastName   = String
type MiddleName = String
data Name = Name FirstName LastName
          | NameWithMiddle FirstName MiddleName LastName

showName :: Name -> String
showName (Name f l) = f ++ " " ++ l
showName (NameWithMiddle f m l) = f ++ " " ++ m ++ " " ++ l

data Sex = Male | Female

showSex :: Sex -> String
showSex Male = "male"
showSex Female = "female"

data RhType = Pos | Neg

showRh :: RhType -> String
showRh Pos = "+"
showRh Neg = "-"

data ABOType = A | B | AB | O

showABO :: ABOType -> String
showABO A = "A"
showABO B = "B"
showABO AB = "AB"
showABO O = "O"

data BloodType = BloodType ABOType RhType

showBloodType :: BloodType -> String
showBloodType (BloodType abo rh) = showABO abo ++ showRh rh

patient1BT :: BloodType
patient1BT = BloodType A Pos

patient2BT :: BloodType
patient2BT = BloodType O Neg

patient3BT::BloodType
patient3BT = BloodType AB Pos

canDonateTo :: BloodType -> BloodType -> Bool
canDonateTo (BloodType O _) _ = True
canDonateTo _ (BloodType AB _) = True
canDonateTo (BloodType A _) (BloodType A _) = True
canDonateTo (BloodType B _) (BloodType B _) = True
canDonateTo _ _ = False

data Patient = Patient  { name :: Name
                        , sex :: Sex
                        , age :: Int
                        , height :: Int
                        , weight :: Int
                        , bloodType :: BloodType }

jackieSmith :: Patient
jackieSmith = Patient { name = Name "Jackie" "Smith"
                      , age = 43
                      , sex = Female
                      , height = 157 
                      , weight = 52
                      , bloodType = BloodType O Neg }

janeESmith :: Patient
janeESmith = Patient { name = NameWithMiddle "Jane" "Elizabet" "Smith"
                     , age = 28
                     , sex = Female
                     , height = 160
                     , weight = 64
                     , bloodType = BloodType AB Neg }

canDonateTo' :: Patient -> Patient -> Bool
canDonateTo' p1 p2 = canDonateTo (bloodType p1) (bloodType p2)

patientSummary :: Patient -> String
patientSummary p = 
    "***********\n" ++
    "Name: " ++ showName (name p) ++ "\n" ++
    "Sex: " ++ showSex (sex p) ++ "\n" ++
    "Age: " ++ show (age p) ++ "\n" ++
    "Height: " ++ show (height p) ++ "cm. \n" ++
    "Weight: " ++ show (weight p) ++ "kg. \n" ++
    "Blood Type: " ++ showBloodType (bloodType p) ++ "\n" ++
    "***********\n"
