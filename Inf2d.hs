-- Inf2D Assignment 1 (Last updated: 25 Jan 2016)

-- Good Scholarly Practice
-- Please remember the University requirement as regards all assessed work for credit.
-- Details about this can be found at:
-- http://www.ed.ac.uk/academic-services/students/undergraduate/discipline/academic-misconduct
-- and at:
-- http://web.inf.ed.ac.uk/infweb/admin/policies/academic-misconduct
-- Furthermore, you are required to take reasonable measures to protect your assessed work from
-- unauthorised access.For example, if you put any such work on a public repository then you must
-- set access permissions appropriately (generally permitting access only to yourself, or your
-- group in the case of group practicals).

module Inf2d where
import Data.List
import Debug.Trace
import Data.Ord
import Data.Maybe
-- Type synonyms for the data structures
-- Symbols are strings (a negative sign as the first character represents a negated symbol)
type Symbol = String
-- Clause = a disjuntion of symbols
type Clause = [Symbol]
-- Sentence = Statements. This is a list of a list of symbols
type Sentence = [[Symbol]]
-- Models are represented as a list of (Symbol,Boolean) tuples
type Model = [(Symbol, Bool)]
-- The knowledge base is represented as a list of statements
type KB = [Sentence]


-----------------------------------------------
-- STUDENT MATRICULATION NUMBER:
-----------------------------------------------
studentId::String
studentId = "s1402967"

--------------------------------------------------
-- ASSIGNMENT TASKS
-- Refer to assignment sheet for details of tasks
--------------------------------------------------

----------TASK 1: REPRESENTATION (2 marks)----------------------------------------------------------
wumpusFact::Sentence
wumpusFact = [["-B11", "P11", "P22", "P31"], ["-P11", "B11"], ["-P22", "B11"], ["-P31", "B11"]]

----------TASK 2: GENERAL HELPER FUNCTIONS (10 marks)-----------------------------------------------

-- Finds the assigned literal to a symbol from a given model
lookupAssignment :: Symbol -> Model -> Maybe Bool
lookupAssignment symbol model
  -- check if the symbol is in the model
  | null [ snd x | x <- model, fst x == symbol ] = Nothing
  | otherwise = Just ( head [ snd x | x <- model, fst x == symbol ] )

-- Negate a symbol
negateSymbol :: Symbol -> Symbol
negateSymbol symbol
  | head symbol == '-' = tail symbol
  | otherwise = "-" ++ symbol

-- For a given symbol, this function checks if it is negated(i.e., has a negation sign).
isNegated :: Symbol -> Bool
isNegated symbol = head symbol == '-'

-- This function takes a symbol and returns an Symbol without any negation sign if the original
-- symbol had one.
getUnsignedSymbol :: Symbol -> Symbol
getUnsignedSymbol symbol
  -- If the symbol is negated then we use the function previously built (i.e. negateSymbol)
  -- to remove the "-" character.
  | isNegated symbol = negateSymbol symbol
  | otherwise = symbol

-- Gets a list of all symbols in for all given sentences
getSymbols :: [Sentence] -> [Symbol]
-- Concatenate the input sentence twice to get a list of all the symbols, map the
-- getUnsignedSymbol to it, in order to avoid negated symbols from being added
-- to the final symbol list and finally, remove duplicates, using another function.
getSymbols stmts = rmDuplicates $ map getUnsignedSymbol $ concat ( concat stmts )

-- Helper function to remove duplicates from a list.
rmDuplicates :: Eq a => [a] -> [a]
rmDuplicates [] = []
rmDuplicates (x:xs)
  | x `elem` xs   = rmDuplicates xs
  | otherwise     = x : rmDuplicates xs

----------TASK 3: TRUTH TABLE ENUMERATION AND ENTAILMENT (40 marks)---------------------------------

-- Function takes as input a list of symbols, and returns a list of models (all possible assignment
-- of True or False to the symbols.)
generateModels :: [Symbol] -> [Model]
generateModels [] = []
generateModels [s] = [[(s, True)], [(s,False)]]
-- Mapping True and False to each symbol given in the input list of symbols, thus forming tuples
-- that are added to the models list.
generateModels (s:symbols) = map (\a->a ++ [(s, True)]) (generateModels symbols) ++ map (\a -> a++ [(s, False)]) (generateModels symbols )

-- This function evaluates the truth value of a propositional sentence using the symbols
-- assignments in the model.
pLogicEvaluate :: Sentence -> Model -> Bool
-- Use a helper function (stmtCheck) for each clause in the statement in order to
-- evaluate it's truth value.
pLogicEvaluate stmts model =  and [ stmtCheck clause model | clause <- stmts ]

-- stmtCheck takes as input a Clause and a Model and returns True if there is a true
-- literal in the clause, hence making the clause true, and False otherwise.
stmtCheck :: Clause -> Model -> Bool
stmtCheck [] _ = False
stmtCheck _ [] = False
stmtCheck (symbol : clause) model
  -- If the symbol is assigned False by the model and it is not negated then keep looking through the clause.
  | (lookupAssignment (getUnsignedSymbol symbol) model == Just False) && not (isNegated symbol) = False || stmtCheck clause model
  -- If the symbol is assigned False by the model and it is negated then return True.
  | (lookupAssignment (getUnsignedSymbol symbol) model == Just False) && isNegated symbol = True
  -- If the symbol is assigned True by the model and it is not negated then return True
  | (lookupAssignment (getUnsignedSymbol symbol) model == Just True) && not (isNegated symbol) = True
  -- If the symbol is assigned True by the model and it is negated then keep looking through the clause.
  | (lookupAssignment (getUnsignedSymbol symbol) model == Just True) && isNegated symbol = False || stmtCheck clause model
  -- If the symbol is not in the model then return False
  | isNothing (lookupAssignment (getUnsignedSymbol symbol) model ) = False
  | otherwise = False

-- This function checks the truth value of list of a propositional sentence using the symbols
-- assignments in the model. It returns true only when all sentences in the list are true.
plTrue :: [Sentence]-> Model -> Bool
-- Since a Sentence is a list of Clauses, we can use pLogicEvaluate to evaluate a sentence,
-- and therefore a list of sentences, using list comprehension.
plTrue sentences model = and [ pLogicEvaluate sentence model | sentence <- sentences ]

-- This function takes as input a knowledgebase (i.e. a list of propositional sentences),
-- a query (i.e. a propositional sentence), and a list of symbols.
-- IT recursively enumerates the models of the domain using its symbols to check if there
-- is a model that satisfies the knowledge base and the query. It returns a list of all such models.
ttCheckAll :: [Sentence] -> Sentence -> [Symbol] -> [Model]
ttCheckAll _ _ [] = []
-- Generates models using the function previously built (i.e. generateModels) and
-- passes the arguments to checkedModels helper function.
ttCheckAll kb query symbols = checkedModels kb query (generateModels symbols)

-- Checks all the models generated and returns only the ones for which the kb entails
-- the query.
checkedModels :: [Sentence] -> Sentence -> [Model] -> [Model]
checkedModels _ _ [] = []
checkedModels kb query (model:models)
  -- Apart from evaluating the query and the knowledge base separately, these also need
  -- to be evaluated with the models generated, hence the use of the evalModel function.
  -- If a model satisfies the knowledge base and the query it is returned and the
  -- function keeps looking through the rest of the model list.
  | evalModel kb query models && pLogicEvaluate query model && plTrue kb model = model : checkedModels kb query models
  | otherwise = checkedModels kb query models

-- Helper function which evaluates if model satisfies the query when the kb is satisfied.
evalModel :: [Sentence] -> Sentence -> [Model] -> Bool
evalModel _ _ [] = True
evalModel kb query (model:models)
  -- If all sentences in the list are true (plTrue condition), the query is evaluated
  -- as well.
  | plTrue kb model = pLogicEvaluate query model && evalModel kb query models
  | otherwise = evalModel kb query models

-- This function determines if a model satisfes both the knowledge base and the query, returning
-- true or false.
ttEntails :: [Sentence] -> Sentence -> Bool
ttEntails kb query
  -- If ttCheckAll retuns an empty list then no model satisfies both the kb and the query,
  -- so it returns the value False.
  | null (ttCheckAll kb query (listSymbols kb query)) = False
  | otherwise = True

-- Helper function used in ttEntails in order to list all the symbols in the kb and query.
listSymbols :: [Sentence] -> Sentence -> [Symbol]
listSymbols [] [] = []
listSymbols [] query = getSymbols [query]
listSymbols (s:kb) [] = getSymbols [[getSymbols [s] ++ getSymbols kb]]
listSymbols (s:kb) query = getSymbols [[getSymbols [query] ++ getSymbols [s] ++ getSymbols kb]]

-- This function determines if a model satisfes both the knowledge base and the query.
-- It returns a list of all models for which the knowledge base entails the query.
ttEntailsModels :: [Sentence] -> Sentence -> [Model]
ttEntailsModels kb query =  [ model | model <- ttCheckAll kb query (listSymbols kb query), pLogicEvaluate query model && plTrue kb model && ttEntails kb query]


----------TASK 4: DPLL (43 marks)-------------------------------------------------------------------

-- The early termination function checks if a sentence is true or false even with a
-- partially completed model.
earlyTerminate :: Sentence -> Model -> Bool
earlyTerminate [] _ = True
-- Checks all clauses in the sentence, using the symbolsInModel function, in order to
-- determine if it can be evaluated.
earlyTerminate (clause:sentence) model
  -- If there is one clause with no symbol that belongs to the model, it returns False.
  | not(symbolsInModel clause model) = False
  | otherwise = earlyTerminate sentence model

-- Checks if there is a symbol in the clause that is part of the model, in order to find out
-- whether the clause can be evaluated or not.
symbolsInModel :: Clause -> Model -> Bool
symbolsInModel [] _ = False
symbolsInModel (symbol:clause) model
  |lookupAssignment (getUnsignedSymbol symbol) model == Just True && not (isNegated symbol) = True
  |lookupAssignment (getUnsignedSymbol symbol) model == Just False && isNegated symbol = True
  |otherwise = symbolsInModel clause model


-- This function finds pure symbol, i.e, a symbol that always appears with the same "sign" in all
-- clauses.
-- It takes a list of symbols, a list of clauses and a model as inputs.
-- It returns Just a tuple of a symbol and the truth value to assign to that
-- symbol. If no pure symbol is found, it should return Nothing
findPureSymbol :: [Symbol] -> [Clause] -> Model -> Maybe (Symbol, Bool)
findPureSymbol [] _ _ = Nothing
findPureSymbol (s:symbols) clauses model
  | isPure s clauses model = Just (s, assignBool s clauses model)
  | otherwise = findPureSymbol symbols clauses model

-- Checks if a symbol is pure, as findPureSymbol goes through all the symbols
-- looking for a pure one.
isPure :: Symbol -> [Clause] -> Model -> Bool
isPure symbol clauses model
  | and [getAssignmentInClause symbol clause | clause <- clauses, not(checkClauseRest symbol clause model)] = True
  | and [not(getAssignmentInClause symbol clause) | clause <- clauses, not(checkClauseRest symbol clause model)] = True
  | otherwise = False

-- The findPureSymbol funtion can also ignore clauses which are already known
-- to be true in the model. So if there is a literal which has a true value then
-- we can stop looking for an impure symbol in that specific clause.
checkClauseRest :: Symbol -> Clause -> Model -> Bool
checkClauseRest _ [] _ = False
checkClauseRest symbol (s:clause) model
  | symbol == getUnsignedSymbol s = checkClauseRest symbol clause model
  | isNegated s && (lookupAssignment (getUnsignedSymbol s) model == Just False) = True
  | not(isNegated s) && (lookupAssignment (getUnsignedSymbol s) model == Just True) = True
  | otherwise = False

-- This function looks for the symbol in the clause and checks whether it is
-- negated or not. This is used by the isPure function, to decide whether all
-- a symbol is consisent throughout all clauses.
getAssignmentInClause :: Symbol -> Clause -> Bool
getAssignmentInClause _ [] = True
getAssignmentInClause symbol (s:clause)
  | symbol == s = True
  | isNegated s && symbol == getUnsignedSymbol s = False
  | otherwise = getAssignmentInClause symbol clause

-- Picks the correct Bool value to be assigned to a pure symbol
assignBool :: Symbol -> [Clause] -> Model -> Bool
assignBool _ [] _ = True
assignBool symbol (clause:clauses) model
  | not (getAssignmentInClause symbol clause) && not(checkClauseRest symbol clause model) = False
  | getAssignmentInClause symbol clause && not(checkClauseRest symbol clause model) = True
  | checkClauseRest symbol clause model = assignBool symbol clauses model
  | otherwise = True


-- This function finds a unit clause from a given list of clauses and a model of assignments.
-- It returns Just a tuple of a symbol and the truth value to assign to that symbol. If no unit
-- clause is found, it should return Nothing.
findUnitClause :: [Clause] -> Model -> Maybe (Symbol, Bool)
findUnitClause [] _ = Nothing
findUnitClause (clause:clauses) model
  -- If the clause contains just one element then that element is returned.
  | length clause == 1 = Just (getUnsignedSymbol (getSymbol clause model), not(isNegated (getSymbol clause model)))
  -- If the number of literals that take the value False is equal to the number of
  -- symbols in the clause minus one, then there must be a true literal in it, and it
  -- is returned.
  | falseLiteralNo clause model == length clause - 1 && getSymbol clause model /= []
    = Just (getUnsignedSymbol (getSymbol clause model), not(isNegated (getSymbol clause model)))
  | otherwise = findUnitClause clauses model

-- Recursively goes through the list of symbols in the model to find one which is True.
getSymbol :: Clause -> Model -> Symbol
getSymbol [] _ = []
getSymbol [symbol] _ = symbol
getSymbol (symbol:clause) model
  -- If the symbol is assigned True by the model and it is not negated, it is returned.
  | getBoolAssignment (getUnsignedSymbol symbol) model && not(isNegated symbol) = symbol
  -- If the symbol is assigned False by the model and it is negated, it is returned.
  | not (getBoolAssignment (getUnsignedSymbol symbol) model) && isNegated symbol = symbol
  | otherwise = getSymbol clause model

-- Gets the Bool value assigned to a symbol in a model. If it is not assigned, then it returns True.
getBoolAssignment :: Symbol -> Model -> Bool
getBoolAssignment symbol model
  | null [ snd x | x <- model, fst x == symbol ] = True
  | otherwise = head [ snd x | x <- model, fst x == symbol ]

-- Returns the no of literals that take a False assignment using the model
-- and whether they are negated or not within the clause.
falseLiteralNo :: Clause -> Model -> Int
falseLiteralNo [] _ = 0
falseLiteralNo (symbol:clause) model
  -- False in model & not negated in clause
  | not (getBoolAssignment (getUnsignedSymbol symbol) model) && not(isNegated symbol) = 1 + falseLiteralNo clause model
  -- true in model & not negated
  | getBoolAssignment (getUnsignedSymbol symbol) model && not(isNegated symbol) = 0 + falseLiteralNo clause model
  -- false in model and negated
  | not (getBoolAssignment (getUnsignedSymbol symbol) model) && isNegated symbol = 0 + falseLiteralNo clause model
  -- true in model and negated
  | getBoolAssignment (getUnsignedSymbol symbol) model && isNegated symbol = 1 + falseLiteralNo clause model
  -- symbol is assigned False so keep looking for a True assigned symbol
  | otherwise = 0

-- This function check the satisfability of a sentence in propositional logic. It takes as input a
-- list of clauses in CNF, a list of symbols for the domain, and model.
-- It returns true if there is a model which satises the propositional sentence.
-- Otherwise it returns false.
dpll :: [Clause] -> [Symbol] -> Bool
dpll _ [] = False
dpll clauses (first:rest)
  -- Checks if all the clauses are true in order to return True.
  | stmtCheckClauses clauses (getModel clauses (generateModels (first:rest))) = True
  -- Checks if all the clauses are false, in order to return False.
  | not (stmtCheckClauses clauses (getModel clauses (generateModels (first:rest)))) = False
  -- If the symbol is pure, it calls the dpll function with the rest of the symbols.
  | isJust p1 = dpll clauses rest
  -- If there is a unit clause, it calls the dpll function with the rest of the symbols.
  | isJust p2 = dpll clauses rest
  | otherwise = dpll clauses rest
  where
    p1 = findPureSymbol [first] clauses (getModel clauses (generateModels rest))
    p2 = findUnitClause clauses (getModel clauses (generateModels rest))

-- Returns a model which satisfies the propositional sentence, using the function
-- stmtCheckClauses.
getModel :: [Clause] -> [Model] -> Model
getModel _ [] = []
getModel clauses (model:models)
  | stmtCheckClauses clauses model = model
  | otherwise = getModel clauses models

-- Helper function used by dpll, which checks if all the clauses are true,
-- using the previously built helper function stmtCheck.
stmtCheckClauses :: [Clause] -> Model -> Bool
stmtCheckClauses clauses model = and [stmtCheck clause model | clause <- clauses]

-- This function serves as the entry point to the dpll function. It takes a list clauses in CNF as
-- input and returns true or false.
-- It uses the dpll function above to determine the satisability of its input sentence.
dpllSatisfiable :: [Clause] -> Bool
dpllSatisfiable clauses = dpll clauses (getSymbols [clauses])

----------TASK 5: EVALUATION (5 marks)--------------------------------------------------------------
-- EVALUATION
-- a knowledge base (i.e. a sentence in propositional
-- logic), and a query sentence. Both items should have their clauses in CNF representation
-- and should be assigned to the following respectively:
evalKB :: [Sentence]
evalKB = [[["a","b"],["d","-b","-c"],["a","c"],["-d"]],[["a","c","d"],["a","-b"],["d","a"]],[["-a","e","f"],["-e","f","b"],["c","b","d"]],[["f","-a","b","d"],["e","c","-d"],["j","f","i"]],[["i","-j","a"],["b","-c","e"],["-j","k","-c"]]]

evalQuery :: Sentence
evalQuery = [["a","-c"],["-d","b"]]


-- RUNTIMES
-- Enter the average runtimes of the ttEntails and dpllSatisable functions respectively
runtimeTtEntails :: Double
runtimeTtEntails = 1044

runtimeDpll :: Double
runtimeDpll = 30
