module LambdaParser where

import Parser
import Data.Lambda
import Data.Builder
-- below is the additional imports
import Data.Char
import Data.Functor

-- You can add more imports if you need them

-- Remember that you can (and should) define your own functions, types, and
-- parser combinators. Each of the implementations for the functions below
-- should be fairly short and concise.


{-|
    Part 1
-}

-- | Exercise 1

-- | Parses a string representing a lambda calculus expression in long form
--
-- >>> parse longLambdaP "(λx.xx)"
-- Result >< \x.xx
--
-- >>> parse longLambdaP "(λx.(λy.xy(xx)))"
-- Result >< \xy.xy(xx)
--
-- >>> parse longLambdaP "(λx(λy.x))"
-- UnexpectedChar '('
--
longLambdaP :: Parser Lambda
longLambdaP = build <$> (foldl1 ap <$> list1 long)
  where
    body = foldl1 ap <$> list1 (fmap term var ||| parens)
    var = satisfy isAsciiLower
    parens = between (is '(') (is ')') (body ||| simpleLong)
    simpleLong = do
      _ <- is 'λ'
      v <- var
      _ <- is '.'
      body' <- body
      return $ v `lam` body'
    long = between (is '(') (is ')') simpleLong ||| simpleLong

-- | Parses a string representing a lambda calculus expression in short form
--
-- >>> parse shortLambdaP "λx.xx"
-- Result >< \x.xx
--
-- >>> parse shortLambdaP "λxy.xy(xx)"
-- Result >< \xy.xy(xx)
--
-- >>> parse shortLambdaP "λx.x(λy.yy)"
-- Result >< \x.x\y.yy
--
-- >>> parse shortLambdaP "(λx.x)(λy.yy)"
-- Result >< (\x.x)\y.yy
--
-- >>> parse shortLambdaP "λxyz"
-- UnexpectedEof

shortLambdaP :: Parser Lambda
shortLambdaP = build <$> (foldl1 ap <$> list1 short)
  where
    var = satisfy (\x -> isAsciiLower x || x == '_')
    body = foldl1 ap <$> list1 (fmap term var ||| parens)
    parens = between (is '(') (is ')') (body ||| simpleShort)
    simpleShort = do
      _ <- is 'λ'
      v <- munch1 (\x -> isAsciiLower x || x == '_')
      _ <- is '.'
      body' <- body
      return $ foldr lam body' v
    short = between (is '(') (is ')') simpleShort ||| simpleShort

-- | Parses a string representing a lambda calculus expression in short or long form
-- >>> parse lambdaP "λx.xx"
-- Result >< \x.xx
--
-- >>> parse lambdaP "(λx.xx)"
-- Result >< \x.xx
--
-- >>> parse lambdaP "λx..x"
-- UnexpectedChar '.'
--

--just a parser combinator of both long and short lambda parser
lambdaP :: Parser Lambda
lambdaP = longLambdaP ||| shortLambdaP 

{-|
    Part 2
-}

-- | Exercise 1

-- IMPORTANT: The church encoding for boolean constructs can be found here -> https://tgdwyer.github.io/lambdacalculus/#church-encodings

-- | Parse a logical expression and returns in lambda calculus
-- >>> lamToBool <$> parse logicP "True and False"
-- Result >< Just False
--
-- >>> lamToBool <$> parse logicP "True and False or not False and True"
-- Result >< Just True
--
-- >>> lamToBool <$> parse logicP "not not not False"
-- Result >< Just True
--
-- >>> parse logicP "True and False"
-- Result >< (\xy.(\btf.btf)xy\_f.f)(\t_.t)\_f.f
--
-- >>> parse logicP "not False"
-- Result >< (\x.(\btf.btf)x(\_f.f)\t_.t)\_f.f
-- >>> lamToBool <$> parse logicP "if True and not False then True or True else False"
-- Result >< Just True

-- boolean logic 
-- take into consideration for space 
logicP :: Parser Lambda
logicP = build <$> logicP'
  where
    logicP' = andOrP ||| notP ||| iteP ||| simpleP
    simpleP = (string "True" $> boolToLam True) ||| (string "False" $> boolToLam False)
    andOrP = do
      a <- simpleP
      space1
      op <- (string "and" $> andL) ||| (string "or" $> orL)
      space1
      b <- logicP'
      return (op `ap` a `ap` b)
    notP = do
      _ <- string "not"
      space1
      (notL `ap`) <$> logicP'
    iteP = do
      _ <- string "if"
      space1
      cond <- logicP'
      space1
      _ <- string "then"
      space1
      a <- logicP'
      space1
      _ <- string "else"
      space1
      b <- logicP'
      return $ iteL `ap` cond `ap` a `ap` b

space1 :: Parser ()
space1 = list1 space $> ()

-- helper function for this part to build the specify lambda 
-- myLam "xy" [term 'x', term 'y'] = \xy.xy
myLam :: [Char] -> [Builder] -> Builder
myLam vars aps = foldr lam (foldl1 ap aps) vars

-- all helper functions needed are define below: 
andL = myLam "xy" [iteL, term 'x', term 'y', falseL]
orL = myLam "xy" [iteL, term 'x', trueL, term 'y']
notL = myLam "x" [iteL, term 'x', falseL, trueL]
iteL = myLam "btf" $ fmap term "btf"
trueL = myLam "t_" [term 't']
falseL = myLam "_f" [term 'f']
succL = myLam "nfx" [term 'f', term 'n' `ap` term 'f' `ap` term 'x']
predL = myLam "nfx" [term 'n', myLam "gh" [term 'h', term 'g' `ap` term 'f'], 'u' `lam` term 'x', 'u' `lam` term 'u']
addL = myLam "xy" [term 'y', succL, term 'x']
minusL = myLam "xy" [term 'y', predL, term 'x']
multiplyL = myLam "xyf" [term 'x', term 'y' `ap` term 'f']
expL = myLam "xy" [term 'y', term 'x']
isZeroL = myLam "n" [term 'n', 'x' `lam` falseL, trueL]
leqL = myLam "xy" [isZeroL, minusL `ap` term 'x' `ap` term 'y']
eqL = myLam "xy" [andL, leqL `ap` term 'x' `ap` term 'y', leqL `ap` term 'y' `ap` term 'x']
neqL = myLam "xy" [notL, eqL `ap` term 'x' `ap` term 'y']
gtL = myLam "xy" [notL, leqL `ap` term 'x' `ap` term 'y']
ltL = myLam "xy" [andL, neqL `ap` term 'x' `ap` term 'y', leqL `ap` term 'x' `ap` term 'y']
geqL = myLam "xy" [notL, ltL `ap` term 'x' `ap` term 'y']
nullL = myLam "cn" [term 'n']
isNullL = myLam "l" [term 'l', myLam "ht" [falseL], trueL]
consL = myLam "htcn" [term 'c', term 'h', term 't' `ap` term 'c' `ap` term 'n']
headL = myLam "l" [term 'l', myLam "ht" [term 'h'], falseL]
tailL = myLam "lcn" [term 'l', myLam "htg" [term 'g', term 'h', term 't' `ap` term 'c'], 't' `lam` term 'n', myLam "ht" [term 't']]


-- | Exercise 2

-- | The church encoding for arithmetic operations are given below (with x and y being church numerals)

-- | x + y = add = λxy.y succ m
-- | x - y = minus = λxy.y pred x
-- | x * y = multiply = λxyf.x(yf)
-- | x ** y = exp = λxy.yx

-- | The helper functions you'll need are:
-- | succ = λnfx.f(nfx)
-- | pred = λnfx.n(λgh.h(gf))(λu.x)(λu.u)
-- | Note since we haven't encoded negative numbers pred 0 == 0, and m - n (where n > m) = 0

-- | Parse simple arithmetic expressions involving + - and natural numbers into lambda calculus
-- >>> lamToInt <$> parse basicArithmeticP "5 + 4"
-- Result >< Just 9
--
-- >>> lamToInt <$> parse basicArithmeticP "5 + 9 - 3 + 2"
-- Result >< Just 13
basicArithmeticP :: Parser Lambda
basicArithmeticP = do
  a <- numP
  xs <- list rightP
  return $ build $ foldl (\x (op, y) -> op `ap` x `ap` y) a xs
  where
    opP = (string "+" $> addL) ||| (string "-" $> minusL)
    rightP = do
      spaces
      op <- opP
      spaces
      b <- numP
      return (op, b)
    numP = intToLam . read <$> munch1 isDigit

-- | Parse arithmetic expressions involving + - * ** () and natural numbers into lambda calculus
-- >>> lamToInt <$> parse arithmeticP "5 + 9 * 3 - 2**3"
-- Result >< Just 24
--
-- >>> lamToInt <$> parse arithmeticP "100 - 4 * 2**(4-1)"
-- Result >< Just 68
arithmeticP :: Parser Lambda
arithmeticP = fmap build $ assoc op3 $ assoc op2 $ assoc op1 baseP
  where
    op1 = string "**" $> expL
    op2 = string "*" $> multiplyL
    op3 = (string "+" $> addL) ||| (string "-" $> minusL)
    numP = intToLam . read <$> munch1 isDigit
    baseP = (lamToBuilder <$> between (is '(') (is ')') arithmeticP) ||| numP

-- assoc op x parses for: x op x op ... op x
-- example:
-- assoc (is '+') (is 'x') can parse: x + x + ... + x
assoc :: Parser Builder -> Parser Builder -> Parser Builder
assoc opP p = do
  a <- p
  xs <- list (rightP p)
  return $ foldl (\x (op, y) -> op `ap` x `ap` y) a xs
  where
    rightP x = do
      spaces
      op <- opP
      spaces
      b <- x
      return (op, b)

-- | Exercise 3

-- | The church encoding for comparison operations are given below (with x and y being church numerals)

-- | x <= y = LEQ = λmn.isZero (minus m n)
-- | x == y = EQ = λmn.and (LEQ m n) (LEQ n m)

-- | The helper function you'll need is:
-- | isZero = λn.n(λx.False)True

-- >>> lamToBool <$> parse complexCalcP "9 - 2 <= 3 + 6"
-- Result >< Just True
--
-- >>> lamToBool <$> parse complexCalcP "15 - 2 * 2 != 2**3 + 3 or 5 * 3 + 1 < 9"
-- Result >< Just False
complexCalcP :: Parser Lambda
complexCalcP = fmap build $ assoc op2 $ withNot $ assoc op1 baseP
  where
    op1 =
      (string "<=" $> leqL)
        ||| (string ">=" $> geqL)
        ||| (string "==" $> eqL)
        ||| (string "!=" $> neqL)
        ||| (string "<" $> ltL)
        ||| (string ">" $> gtL)
    op2 = (string "and" $> andL) ||| (string "or" $> orL)
    baseP = fmap lamToBuilder $ between (is '(') (is ')') complexCalcP ||| arithmeticP ||| logicP
    withNot' x = do
      string "not"
      space1
      v <- withNot x
      return $ notL `ap` v
    withNot x = withNot' x ||| x


{-|
    Part 3
-}

-- | Exercise 1

-- | The church encoding for list constructs are given below
-- | [] = null = λcn.n
-- | isNull = λl.l(λht.False) True
-- | cons = λhtcn.ch(tcn)
-- | head = λl.l(λht.h) False
-- | tail = λlcn.l(λhtg.gh(tc))(λt.n)(λht.t)
--
-- >>> parse listP "[]"
-- Result >< \cn.n
--
-- >>> parse listP "[True]"
-- Result >< (\htcn.ch(tcn))(\xy.x)\cn.n
--
-- >>> parse listP "[0, 0]"
-- Result >< (\htcn.ch(tcn))(\fx.x)((\htcn.ch(tcn))(\fx.x)\cn.n)
--
-- >>> parse listP "[0, 0"
-- UnexpectedEof
listP :: Parser Lambda
listP = between (is '[') (is ']') (build . foldr (\h t -> consL `ap` h `ap` t) nullL <$> sep "," baseP)
  where
    baseP = (string "True" $> trueL') ||| (string "False" $> falseL) ||| fmap lamToBuilder arithmeticP
    -- this variable is used to adapt the test case
    trueL' = myLam "xy" [term 'x']
    -- sep is parse for list with separators
    sep s x = sep' s x ||| return []
    sep' s x = do
      v <- x
      spaces
      vs <- list $ sepRight s x
      return (v : vs)
    sepRight s x = do
      string s
      spaces
      v <- x
      spaces
      return v

-- >>> lamToBool <$> parse listOpP "head [True, False, True, False, False]"
-- Result >< Just True
--
-- >>> lamToBool <$> parse listOpP "head rest [True, False, True, False, False]"
-- Result >< Just False
--
-- >>> lamToBool <$> parse listOpP "isNull []"
-- Result >< Just True
--
-- >>> lamToBool <$> parse listOpP "isNull [1, 2, 3]"
-- Result >< Just False
listOpP :: Parser Lambda
listOpP = do
  x <- baseP
  xs <- list (space1 *> baseP)
  return $ build $ foldr1 ap (x : xs)
  where
    -- assume head rest x is equivalent to head (rest x)
    -- and assume rest is tail
    opP =
      (string "head" $> headL)
        ||| (string "tail" $> tailL)
        ||| (string "rest" $> tailL)
        ||| (string "isNull" $> isNullL)
    baseP = opP ||| fmap lamToBuilder listP


-- | Exercise 2

-- | Implement your function(s) of choice below!
