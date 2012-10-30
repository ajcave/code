import Control.Monad.ST
import Data.STRef
import Control.Monad

data Type s = 
	  Int
	| Bool
	| Arrow (Type s) (Type s)
	| Product (Type s) (Type s)
	| TVar (STRef s (Maybe (Type s)))
          deriving Eq

occurs _ Int = return False
occurs _ Bool = return False
occurs s (Arrow t1 t2) =  liftM2 (||) (occurs s t1) (occurs s t2)
occurs s (Product t1 t2) = liftM2 (||) (occurs s t1) (occurs s t2)
occurs s t@(TVar x) = do
	y <- readSTRef x
	case y of
	  Nothing -> return (s == t) 
	  Just t' -> liftM2 (||) (return (s == t)) (occurs s t')

unify Int Int = return ()
unify Bool Bool = return ()
unify (Arrow s1 s2) (Arrow t1 t2) = do
	unify s1 t1
	unify s2 t2
unify (Product s1 s2) (Product t1 t2) = do
	unify s1 t1
	unify s2 t2
unify s@(TVar x) t = helper t s x
unify t s@(TVar x) = helper t s x
unify _ _ = error "Cannot unify"

-- This is buggy (rtest2 diverges) and I'm not sure why. Oh. it relies on the occurs check when we set one variable to point to the other
helper t s x = do
  xv <- readSTRef x
  case xv of
    Just s' -> unify t s'
    Nothing -> if t == s then return () else writeSTRef x (Just t)

data PType = 
	  PInt
	| PBool
	| PArrow PType PType
	| PProduct PType PType
	| PTVar Integer 
          deriving (Show, Eq)

purify Int l = return (PInt,l)
purify Bool l = return (PBool,l)
purify (Arrow t1 t2) l = do
	(t1',l') <- purify t1 l
	(t2',l'') <- purify t2 l'
	return (PArrow t1' t2', l'')
purify (Product t1 t2) l = do
	(t1',l') <- purify t1 l
	(t2',l'') <- purify t2 l'
	return (PProduct t1' t2', l'')
purify (TVar x) (n,l) = do
	xv <- readSTRef x
	case xv of
	  Nothing -> case lookup x l of
	              Nothing -> return (PTVar n, (n+1, (x,n):l))
	              Just m -> return (PTVar m, (n,l))
	  Just t -> purify t (n,l)

purify' t = do
	(pt, _) <- purify t (0,[])
	return pt

punify t1 t2 = do
	unify t1 t2
	pt1 <- purify' t1
	pt2 <- purify' t2
	return (pt1, pt2)

test1 = do
	a <- newSTRef Nothing
	b <- newSTRef Nothing
	let t1 = Arrow (Product (TVar a) (TVar a)) (TVar b)
	    t2 = Arrow (Product Int Int) (TVar a)
	punify t1 t2

rtest1 = runST test1

test2 = do
	a <- newSTRef Nothing
	b <- newSTRef Nothing
	let t1 = Arrow (Product (TVar a) (TVar b)) (TVar b)
	    t2 = Arrow (Product (TVar b) (TVar a)) (TVar a)
	punify t1 t2

rtest2 = runST test2

test3 = do
	a <- newSTRef Nothing
	b <- newSTRef Nothing
	let t1 = Arrow (Product (TVar a) (TVar b)) (TVar b)
	    t2 = Arrow (TVar b) (TVar a)
	punify t1 t2

rtest3 = runST test3
