{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- Imports for Monads

import Control.Monad

-- AST and Type Definitions
data TEAM12 where
  Num :: Int -> TEAM12
  Boolean :: Bool -> TEAM12
  Id :: String -> TEAM12
  Plus :: TEAM12 -> TEAM12 -> TEAM12
  Minus :: TEAM12 -> TEAM12 -> TEAM12
  Mult :: TEAM12 -> TEAM12 -> TEAM12
  Div :: TEAM12 -> TEAM12 -> TEAM12
  Lambda :: String -> TTEAM12 -> TEAM12 -> TEAM12 
  Bind :: String -> TEAM12 -> TEAM12 -> TEAM12
  App :: TEAM12 -> TEAM12 -> TEAM12
  Fix :: TEAM12 -> TEAM12
  And :: TEAM12 -> TEAM12 -> TEAM12
  Or :: TEAM12 -> TEAM12 -> TEAM12
  Leq :: TEAM12 -> TEAM12 -> TEAM12
  IsZero :: TEAM12 -> TEAM12
  If :: TEAM12 -> TEAM12 -> TEAM12 -> TEAM12
  deriving (Show,Eq)

data TTEAM12 where
    TNum :: TTEAM12
    TBool :: TTEAM12
    (:->:) :: TTEAM12 -> TTEAM12 -> TTEAM12
    TUnit :: TTEAM12
    deriving (Show,Eq)

data VALUELANG where
  NumV :: Int -> VALUELANG
  BoolV :: Bool -> VALUELANG
  ClosureV :: String -> TEAM12 -> ValueEnv -> VALUELANG
  deriving (Show,Eq)
 
data EXTLANG where
  NumX :: Int -> EXTLANG
  PlusX :: EXTLANG -> EXTLANG -> EXTLANG
  MinusX :: EXTLANG -> EXTLANG -> EXTLANG
  MultX :: EXTLANG -> EXTLANG -> EXTLANG
  DivX :: EXTLANG -> EXTLANG -> EXTLANG
  If0X :: EXTLANG -> EXTLANG -> EXTLANG -> EXTLANG
  LambdaX :: String -> TTEAM12 -> EXTLANG -> EXTLANG
  AppX :: EXTLANG -> EXTLANG -> EXTLANG
  FixX :: EXTLANG -> EXTLANG
  BindX :: String -> EXTLANG -> EXTLANG -> EXTLANG
  IdX :: String -> EXTLANG
  Composite :: EXTLANG -> EXTLANG -> EXTLANG -> EXTLANG
  deriving (Show,Eq)

type Cont = [(String,TTEAM12)]
type TermEnv = [(String,TEAM12)]
type ValueEnv = [(String,VALUELANG)]

-- need subst to add fix

subst :: String -> TEAM12 -> TEAM12 -> TEAM12
subst i v (Num x) = (Num x)
subst i v (Plus l r) = (Plus (subst i v l) (subst i v r))
subst i v (Minus l r) = (Minus (subst i v l) (subst i v r))
subst i v (Mult l r) = (Mult (subst i v l) (subst i v r))
subst i v (Div l r) = (Div (subst i v l) (subst i v r))
subst i v (Boolean b) = (Boolean b)
subst i v (And l r) = (And (subst i v l) (subst i v r))
subst i v (Or l r) = (Or (subst i v l) (subst i v r))
subst i v (Leq l r) = (Leq (subst i v l) (subst i v r))
subst i v (IsZero l) = (IsZero (subst i v l))
subst i v (If p t e) = (If (subst i v p) (subst i v t) (subst i v e))
subst i v (Id i') = if i==i' then v else (Id i')
subst i v (Bind i' v' b') = if i==i' then (Bind i' (subst i v v') b') else (Bind i' (subst i v v') (subst i v b'))
subst i v (Lambda i' t b) = if i==i' then (Lambda i' t b) 
                                   else (Lambda i' t (subst i v b))
subst i v (App f a) = (App (subst i v f) (subst i v a))
subst i v (Fix f) = (Fix (subst i v f))

-- Part 1: Type Inference

typeofM :: Cont -> TEAM12 -> (Maybe TTEAM12)
typeofM c (Num n) = if n>=0 then return TNum else Nothing
typeofM c (Boolean b) = return TBool
typeofM c (Plus l r) = do {TNum <- typeofM c l;
                        TNum <- typeofM c r; 
                        return TNum;} 
typeofM c (Minus l r) = do {TNum <- typeofM c l;
                        TNum <- typeofM c r; 
                        return TNum;} 
typeofM c (Mult l r) = do {TNum <- typeofM c l;
                        TNum <- typeofM c r; 
                        return TNum;} 
typeofM c (Div l r) = do {TNum <- typeofM c l;
                        TNum <- typeofM c r; 
                        return TNum;} 
typeofM c (And l r) = do {TBool <- typeofM c l;
                        TBool <- typeofM c r; 
                        return TBool;}
typeofM c (Or l r) = do {TBool <- typeofM c l;
                        TBool <- typeofM c r; 
                        return TBool;}
typeofM c (Leq l r) = do {TNum <- typeofM c l;
                        TNum <- typeofM c r; 
                        return TBool;}
typeofM c (IsZero l) = do {TNum <- typeofM c l; 
                        return TBool;}  
typeofM cont (If c t e) = do {TBool <- typeofM cont c;
                        t' <- typeofM cont t;
                        e' <- typeofM cont e;
                        if (t' == e') then 
                            Just t';
                        else
                            Nothing} 
typeofM c (Bind i v b) = do { v' <- (typeofM c v);
                            typeofM ((i,v'):c) b;
                            }
typeofM c (Id i) = (lookup i c)
typeofM c (Lambda x t b) = do { tyB <- typeofM ((x,t):c) b ;
                                  return (t :->: tyB) }
typeofM cont (App x y) = do { tyXd :->: tyXr <- typeofM cont x ;
                             tyY <- typeofM cont y ;
                             if tyXd==tyY
                             then return tyXr
                             else Nothing }
typeofM c (Fix t) = do { (d :->: r) <- typeofM c t;
                         return r }

-- Part 2: Evaluation
evalM :: ValueEnv -> TEAM12 -> (Maybe VALUELANG)
evalM env (Boolean b) = Just (BoolV b)
evalM env (Num x) = if x<0 then Nothing else Just (NumV x)
evalM env (Minus l r) = do {(NumV l') <- evalM env l;
                (NumV r') <- evalM env r;
                if(l' >= r') then 
                     return (NumV (l'-r')) 
                     else 
                     Nothing}
evalM env (Plus l r) = do {(NumV l') <- evalM env l;
                (NumV r') <- evalM env r;
                return (NumV (l'+r'))}
evalM env (Mult l r) = do {(NumV l') <- evalM env l;
                (NumV r') <- evalM env r;
                return (NumV (l'*r'))}
evalM env (Div l r) = do {(NumV l') <- evalM env l;
                (NumV r') <- evalM env r;
                if(r' /= 0) then 
                    return (NumV (l' `div` r')) 
                    else 
                        Nothing}
evalM env (If c t l) = do {(NumV 0) <- evalM env c;
                 (t') <- evalM env t;
                 (l') <- evalM env l;
                 if (False) then
                     return t'
                     else
                         return l'}
evalM env (Id i) = (lookup i env)
evalM env (Lambda x i b) = return (ClosureV x b env)
evalM env (App f a) = do { (ClosureV i b j) <- evalM env f;
                         v <- evalM env a;
                         evalM ((i,v):j) b}
evalM env (Fix f) = do { (ClosureV i b env') <- evalM env f;
                         evalM env' (subst i (Fix (Lambda i TUnit b)) b) }
evalM env (Bind i v b) = do { v' <- (evalM env v) ;
                             evalM ((i,v'):env) b }
evalM env (And l r) = do{(BoolV l') <- evalM env l;
                     (BoolV r') <- evalM env r;
                     return (BoolV(l' && r')) }
evalM env (Or l r) = do{(BoolV l') <- evalM env l;
                     (BoolV r') <- evalM env r;
                     return (BoolV(l' || r')) }
evalM env (Leq l r) = do{(NumV l') <- evalM env l;
                     (NumV r') <- evalM env r;
                     return (BoolV(l' <= r')) }
evalM env (IsZero l) = do{(NumV l') <- evalM env l;
                     return (BoolV(l' == 0)) }
                     
-- Part 4: Extra lang feature
evalTerm :: ValueEnv -> EXTLANG -> (Maybe VALUELANG)
evalTerm a b = do{
evalM a (elabTerm b)
}

elabTerm :: EXTLANG -> TEAM12
elabTerm (NumX x) = Num x
elabTerm (PlusX l r) = Plus (elabTerm l)(elabTerm r)
elabTerm (MinusX l r) = Minus (elabTerm l)(elabTerm r)
elabTerm (MultX l r) = Mult (elabTerm l)(elabTerm r)
elabTerm (DivX l r) = Div (elabTerm l)(elabTerm r)
elabTerm (If0X a b c) =If (elabTerm a)(elabTerm b)(elabTerm c)
elabTerm (LambdaX x i b) = (Lambda x i (elabTerm b))
elabTerm (AppX f a) = App (elabTerm f)(elabTerm a)
elabTerm (IdX i) = Id i
elabTerm (BindX i v b) = (Bind i (elabTerm b) (elabTerm v))
elabTerm (Composite f g a) = App (elabTerm f) (App (elabTerm g) (elabTerm a))

main = do
    print "--------------------*  typeofM *--------------------"
    print $ typeofM [] (Bind "blake" (Boolean True) (If (Id "blake") (Boolean True) (Boolean False)))
    print $ typeofM [] (Bind "blake" (Num 5) (Bind "Blake" (Num 7) (Plus (Id "blake") (Id "Blake"))))
    print $ typeofM [] (Lambda "x" TNum (Plus (Id "x") (Num 5)))
    print $ typeofM [] (Lambda "x" TBool (If (Id "x") (Num 5) (Num 10)))
    print $ typeofM [] (App (Lambda "x" TNum (Plus (Id "x") (Num 5))) (Num 5))
    print $ typeofM [] (App (Lambda "x" TBool (If (Id "x") (Num 5) (Num 10))) (Boolean True))
    print("eval (lambda x in x+1)(lambda x in x+2)(3) = " ++ show (evalTerm [] (Composite 
                                                              (LambdaX "x" TNum (MultX (IdX "x")(NumX 5)))
                                                              (LambdaX "x" TNum (PlusX (IdX "x")(NumX 2)))
                                                              (NumX 3)
                                                            )
                                                ));

    print "--------------------*  evalM  *--------------------"
    -- print $ evalM [] (Plus (Num 5) (Num 10))
    print $ evalM [] (Lambda "x" TNum (Plus (Id "x") (Num 5)))
    print $ evalM [] (App (Lambda "x" TNum (Plus (Id "x") (Num 5))) (Num 5))
    print $ evalM [] (App (Lambda "x" TNum (Plus (Id "x") (Num 10))) (Num 5))
    print $ evalM [] (Bind "blake" (Num 5) (Bind "Blake" (Num 7) (Plus (Id "blake") (Id "Blake"))))

