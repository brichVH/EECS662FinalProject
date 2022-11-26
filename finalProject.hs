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
  LambdaX :: String -> EXTLANG -> EXTLANG
  AppX :: EXTLANG -> EXTLANG -> EXTLANG
  BindX :: String -> EXTLANG -> EXTLANG -> EXTLANG
  IdX :: String -> EXTLANG
  deriving (Show,Eq)

type Cont = [(String,TTEAM12)]
type TermEnv = [(String,TEAM12)]
type ValueEnv = [(String,VALUELANG)]

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

main = do
    print "--------------------*  typeofM *--------------------"
    print $ typeofM [] (Bind "blake" (Boolean True) (If (Id "blake") (Boolean True) (Boolean False)))
    print $ typeofM [] (Bind "blake" (Num 5) (Bind "Blake" (Num 7) (Plus (Id "blake") (Id "Blake"))))
    print $ typeofM [] (Lambda "x" TNum (Plus (Id "x") (Num 5)))
    print $ typeofM [] (Lambda "x" TBool (If (Id "x") (Num 5) (Num 10)))
    print $ typeofM [] (App (Lambda "x" TNum (Plus (Id "x") (Num 5))) (Num 5))
    print $ typeofM [] (App (Lambda "x" TBool (If (Id "x") (Num 5) (Num 10))) (Boolean True))

    print "--------------------*  evalM  *--------------------"
    -- print $ evalM [] (Plus (Num 5) (Num 10))
    print $ evalM [] (Lambda "x" TNum (Plus (Id "x") (Num 5)))
    print $ evalM [] (App (Lambda "x" TNum (Plus (Id "x") (Num 5))) (Num 5))
    print $ evalM [] (App (Lambda "x" TNum (Plus (Id "x") (Num 10))) (Num 5))
    print $ evalM [] (Bind "blake" (Num 5) (Bind "Blake" (Num 7) (Plus (Id "blake") (Id "Blake"))))

