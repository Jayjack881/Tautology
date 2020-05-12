{-
 - Author: Ritisha Sharma, rsharma2017@my.fit.edu
 - Course: CSE 4250, Fall 2019
 - Project: Proj4, Tautology Checker
 - Language implementation: Glorious Glasgow Haskell Compilation System, version 8.4.3
 -}

module Main where

    import Data.List()
    -- Define the leaf and each operation of the expression tree
    data ExprTree = Operand Char
        | Disjunction ExprTree ExprTree
        | Implication ExprTree ExprTree
        | Nand        ExprTree ExprTree
        | Equivalence ExprTree ExprTree
        | Negation    ExprTree 
        | Xor         ExprTree ExprTree
        | Conjunction ExprTree ExprTree  
        
    -- Function to traverse the tree and form the final expression
    formExp :: ExprTree -> [Char]
    formExp (Operand x) = [x]
    formExp (Negation x)      = "~"  ++ formExp x
    formExp (Disjunction l r) = "(" ++ formExp l ++  " V "  ++ formExp r ++ ")"
    formExp (Implication l r) = "(" ++ formExp l ++  " => " ++ formExp r ++ ")"
    formExp (Nand l r)        = "(" ++ formExp l ++  " | "  ++ formExp r ++ ")"
    formExp (Equivalence l r) = "(" ++ formExp l ++ " <=> " ++ formExp r ++ ")"
    formExp (Xor l r)         = "(" ++ formExp l ++  " + "  ++ formExp r ++ ")"
    formExp (Conjunction l r) = "(" ++ formExp l ++  " & "  ++ formExp r ++ ")"

    -- Check if the letter is an operator
    isOperator :: Char -> Bool
    isOperator n = n `elem` "ACDEFJK"

    -- Convert to Negation Normal Form
    toNNF :: ExprTree -> ExprTree
    -- Base cases
    toNNF (Operand x)                     = Operand x -- If the leaf reached, nothing needs to be done
    toNNF (Negation (Negation x))         = toNNF x -- Double negation
    -- Recursive cases
    toNNF (Conjunction x n)               = Conjunction (toNNF x) (toNNF n)    
    toNNF (Negation (Conjunction x n))    = Disjunction (toNNF (Negation x)) (toNNF (Negation n))
    toNNF (Disjunction x n)               = Disjunction (toNNF x) (toNNF n)
    toNNF (Negation (Disjunction x n))    = Conjunction (toNNF (Negation x)) (toNNF (Negation n))
    toNNF (Implication x n)               = Disjunction (toNNF (Negation x)) (toNNF n)
    toNNF (Negation (Implication x n))    = Conjunction (toNNF x) (toNNF (Negation n))
    toNNF (Equivalence x n)               = let a = Disjunction (Negation x) (n)
                                                b = Disjunction (x) (Negation n)
                                            in toNNF (Conjunction a b)
    toNNF (Negation (Equivalence x n))    = let a = Conjunction (Negation x) (n)
                                                b = Conjunction (x) (Negation n)
                                            in toNNF (Disjunction a b)
    toNNF (Negation x)                    = Negation x
    -- Convert to more familiar operations
    toNNF (Nand x n)                      = toNNF (Negation (Conjunction x n)) 
    toNNF (Xor x n)                       = toNNF (Conjunction (Disjunction x n) (Disjunction (Negation x) (Negation n)))

    -- Convert to Conjunctive Normal Form
    toCNF :: ExprTree -> ExprTree
    toCNF (Conjunction x n) = Conjunction (toCNF x) (toCNF n)
    toCNF (Disjunction x n) = distribute (toCNF x) (toCNF n)
    toCNF x                 = x

    -- Function to distrubute operations
    distribute :: ExprTree -> ExprTree -> ExprTree
    distribute (Conjunction x y) z = Conjunction (distribute x z) (distribute y z)
    distribute z (Conjunction x y) = Conjunction (distribute z x) (distribute z y)
    distribute x y                 = Disjunction (x) (y)

    -- Check if expression tree represents a tautology
    isTautology :: (ExprTree, Bool)-> Bool
    isTautology ( _, True)              = True 
    isTautology (Disjunction x y, _ )   = let a = Disjunction x y
                                        in findOperand (a) (a) -- P OR NOT P will always be true
    isTautology (Conjunction x y, _ )   = isTautology (x, False) && isTautology (y, False) -- Find the clauses separated by conjunctions
    isTautology ( _ , _ )               = False

    -- Create a list of operands in one tree
    findOperand :: ExprTree -> ExprTree -> Bool
    findOperand (org) (Operand x)           = checkComplement (org) (x) -- If the leaf is reached then check if it has a complement
    findOperand (org) (Disjunction x y)     = findOperand (org) (x) || findOperand (org) (y) -- If any recursive returns true the whole function return true
    findOperand (_) (_)                     = False

    checkComplement :: ExprTree -> Char -> Bool
    checkComplement (Negation (Operand x)) (c) = if x == c then True else False -- Find matching character that is negated
    checkComplement (Disjunction x y) (c) = checkComplement (x) (c) || checkComplement (y) (c)
    checkComplement (_) (_) = False
    
    toString :: Bool -> String
    toString (True)  = "true"
    toString (False) = "false"

    addLeaf :: Char -> [ExprTree] -> [ExprTree]
    addLeaf x xs = Operand (x) : xs

    -- Uses a stack to turn the postfix expression into an infix expression tree
    toInfix :: [ExprTree] -> [Char] -> ExprTree
    toInfix xs input
        | length input == 0                 = head xs
        | length xs == 0 || length xs == 1  = toInfix (addLeaf x xs) (tail input)
        | x == 'F'                          = toInfix (perform : tail xs) (tail input)
        | isOperator(x) == True             = toInfix (perform : tail (tail xs)) (tail input)
        | otherwise                         = toInfix (Operand (x) : xs) (tail input)
        where 
            x = head (input)
            perform :: ExprTree
            perform
                | head (input) == 'A'   = Disjunction (head (tail xs)) (head xs)
                | head (input) == 'C'   = Implication (head (tail xs)) (head xs)
                | head (input) == 'D'   = Nand (head (tail xs)) (head xs)
                | head (input) == 'E'   = Equivalence (head (tail xs)) (head xs)
                | head (input) == 'F'   = Negation (head xs) 
                | head (input) == 'J'   = Xor (head (tail xs)) (head xs)
                | head (input) == 'K'   = Conjunction (head (tail xs)) (head xs)  
                | otherwise             = head xs

    main :: IO ()
    main = interact (eachLine tautologyCheck)

    eachLine :: (String -> String) -> (String -> String)
    eachLine f = unlines . map f . lines

    -- collects and formats the final output
    tautologyCheck :: String -> String
    tautologyCheck line = do
    toString (isTautology (tree, False)) ++ " " ++ formExp (tree) 
            where
                tree = toCNF (toNNF (toInfix stack line))
                stack = []

