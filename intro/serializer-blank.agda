module serializer-blank where
open import helper
open import Data.String
open import Data.Bool
open import Data.Nat.Show


-- Serializing data (i.e. converting data to strings to write them to disk) is boring and repetitive
-- Here's how we would probably do it in SML (or Java or ...)

-- SML: datatype IsManager = Nope | Yep of string
data IsManager : Type where
 Nope : IsManager
 Yep : (dept : String) -> IsManager

-- SML: datatype Employee = Empl of string * IsManager * int
data Employee : Type where
 Empl : (name : String) -> (m : IsManager) -> (birthyear : number) -> Employee

-- SML: datatype Province = Quebec | Alberta | ....
data Province : Type where
 Quebec : Province
 Alberta : Province
 -- ...

-- SML: datatype Department = Dept of string * Province
data Department : Type where
 Dept : (name : String) -> (location : Province) -> Department
  
isManagerToString : IsManager -> String
isManagerToString Nope = "Nope"
isManagerToString (Yep dept) = "Yep: " ++ dept

emplToString : Employee -> String
emplToString (Empl name m birthyear) =
 "(" ++ name ++ "," ++ isManagerToString m ++ "," ++ show birthyear ++ ")"

-- SML : val johnEg = Empl ("John Smith", Nope, 04)
johnEg = Empl "John Smith" Nope 04

johnStringEg = emplToString johnEg

janeEg = Empl "Jane Smith" (Yep "Cybernetics") 03

janeStringEg = emplToString janeEg

parseEmpl : String -> option Employee
parseEmpl s = {!... bleh ...!}

provinceToString : Province -> String
provinceToString Quebec = "Quebec"
provinceToString Alberta = "Alberta"

deptToString : Department -> String
deptToString (Dept name location) = "(" ++ name ++ "," ++ provinceToString location ++ ")"

cybEg = Dept "Cybernetics" Quebec

cybString = deptToString cybEg

parseDept : String -> option Department
parseDept s = {!... bleh ...!}

-- This is really boring, and for every new datatype we want to serialize, we have
-- to write the same kind of repetitive function.
-- Even worse if we want to write the parser that reads data back in from strings!
-- Couldn't we just say how to serialize datatypes to strings once and for all?
-- There are some large, complicated libraries for (e.g.) Java which do this...

-- Can we do better with dependent types?
-- Yes! In ~30 lines! So we can understand how it works and extend it or customize
-- it ourselves

infixr 9 _⊗_

-- Let's write down a datatype describing the kinds of types we want
-- to be able to serialize to strings.
-- This is like how we had a datatype describing datatypes in HW5
data Datatype : Type  where
 -- base types
 bool : Datatype
 int : Datatype
 string : Datatype
 unit : Datatype
 -- Fancy symbol for Product i.e. *
 _⊗_ : (T1 : Datatype) -> (T2 : Datatype) -> Datatype
 -- Like SML's:   Empty of 'a | Node of ('a tree * 'a tree) datatypes
 _of_∣_of_ : (l1 : String) -> (T1 : Datatype) -> (l2 : String) -> (T2 : Datatype) -> Datatype

-- Now we write down "encodings" or *descriptions* of our datatypes:
isManager : Datatype
isManager = ("Yep" of string ∣ "Nope" of unit)
                   -- department
employee : Datatype
employee = string ⊗ isManager ⊗ int
        -- Name, Is Manager of department, Birth year

province : Datatype
province = "Quebec" of unit ∣ "Alberta" of unit

department : Datatype
department = string ⊗ province   -- name, location

-- Here's the magic part:
-- We compute from a datatype description an honest, real Agda datatype!
-- You can't do this in SML (Or any commercial language..)
interpret : Datatype -> Type
interpret T = {!!}
-- Hopefully you have questions...

egInterpret1 = interpret isManager

egInterpret2 = interpret employee

john : interpret employee
john = "John Smith" , (right 〈〉) , 04

jane : interpret employee
jane = "Jane Smith" , (left "Cybernetics") , 03

cybernetics : interpret department
cybernetics = "Cybernetics", (left 〈〉) -- Quebec

-- Now we can write a toString once and for all
-- for every datatype!
-- We take in a description of the datatype, and then
-- a *value* of that datatype, and return a string:
toString : (T : Datatype) -> interpret T -> String
toString T x = {!!}

johnString = toString employee john

janeString = toString employee jane

cyberString = toString department cybernetics

-- toString will work automatically for every new Datatype we write!

-- Could even implement a parser once and for all too!
parse : (T : Datatype) -> String -> option (interpret T)
parse T s = {! ... bleh ...!}

-- The same technique works for writing database code
-- You can write once and for all a generic (SQL) query which
-- reads (writes) any kind of datatype from the database
-- Or serializing to XML, etc...


