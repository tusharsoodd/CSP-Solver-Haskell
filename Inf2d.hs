




module Inf2d where

import Data.List
import Data.Maybe
import CSPframework
import Examples


-------------------------------------------------
-- (3) Sudoku problem
-------------------------------------------------

-- (3.i) Variables & values

{-# LANGUAGE BlockArguments #-}

queenVars :: Int -> [Var]
queenVars x = ["Q" ++ show i | i <- [1..x]]

squares = [0..64]

queenDomains :: Int -> Domains
queenDomains n = map (\r -> (r,squares)) (queenVars n)


-- (3.ii) Constraints

extractAssignments :: Assignment -> [Int]                                      --takes out the number cell each queen is assigned to and makes a list
extractAssignments ys = [varValue y|y<-ys]

isEdge :: Int -> Bool    --checks if a given positiion on the chess board is on the edge of the board
isEdge x | x `mod` 8 == 0 || x `elem` [0,1,2,3,4,5,6,7,15,23,31,39,47,55,63] = True
		 | otherwise = False


--Getting an error about indentation, so can't load this.
-- diagonalRelation :: Relation -- ensures for a given assignment that no queen can attack another queen diagonally 
-- diagonalRelation vs ass = and [checkUp (varValue(a)-9) (extractAssignments ass) && checkDown (varValue(a)+9) (extractAssignments ass) | a<-ass]
    -- where
        -- checkDown :: Int -> [Int] -> Bool
		-- checkDown x ls | (x `elem` ls) == False && isEdge x = False
                       -- | (x `elem` ls) == True = True
                       -- | otherwise = checkUp x+9 ls
					   
		-- checkUp :: Int -> [Int] -> Bool  --check that a queen is not in the way of another queen to the top right or top left 
        -- checkUp x ls | (x `elem` ls) == False && isEdge x = False
                     -- | (x `elem` ls) = True 
                     -- | otherwise = (checkUp x-9 ls)
					 
		

				

		

-- verticalRelation :: Relation  --ensures that no queen can attack another queen vertically
-- verticalRelation vs ass = and [checkUp(varValue(a)-8 extractAssignments ass) && checkDown(varValue(a)+8 extractAssignments ass) | a<-ass]
	-- where
		-- checkUp :: Int -> [Int] -> Bool  --checks if 
		-- checkUp x ls | (x `elem` ls) == False && isEdge x = False
			         -- | (x `elem` ls) = True 
			         -- | otherwise = checkUp x-8 ls

		-- checkDown :: Int -> [Int] -> Bool
		-- checkDown x ls | (x `elem` ls) == False && isEdge x = False
			           -- | (x `elem` ls) = True 
			           -- | otherwise = checkUp x+8 ls

-- horizontalRelation :: Relation  --ensures that no queen can attack another queen horizontally
-- horizontalRelation vs ass = and [checkLeft(varValue(a)-1 extractAssignments ass) && checkRight(varValue(a)+1 extractAssignments ass) | a<-ass]
	-- where
		-- checkLeft:: Int -> [Int] -> Bool  --checks if 
		-- checkLeft x ls | (x `elem` ls) == False && isEdge x = False
			           -- | (x `elem` ls) = True 
			           -- | otherwise = checkLeft x-1 ls

		-- checkRight :: Int -> [Int] -> Bool
		-- checkRight x ls | (x `elem` ls) == False && isEdge x = False
			            -- | (x `elem` ls) = True 
			            -- | otherwise = checkRight x+1 ls

	 

-- Binary constraint stating that two variables differ by exactly n.
-- diagonalConstraint :: Var -> Var -> Constraint
-- diagonalConstraint a b = CT (a ++ " and " ++ b ++ " not in the same diagonal",[a,b],diagonalRelation)



-- (3.iii) N-Queens CSP

--queenCsp :: Int -> CSP
--queenCsp n = CSP ((show n) ++ "-Queens Problem",
--             queenDomains n, [
--               {allDiffConstraint queenVars
				
				
			   
			   
			   
			   
			   
--		   }
  --             ])



-------------------------------------------------
-- (4.1) Forward Checking
-------------------------------------------------

-- (4.1.i) Forward check for infernce:


forwardcheck :: CSP -> Assignment -> Var -> (CSP,Bool)
forwardcheck cspa assignments var = deleteInconsistentValues assignments cspa var (allNeighboursOf var cspa) True    -- passing in the csp, assignments, variable and its undeclared neighbours        (filter (\x -> x `notElem` (fst assignments)) (allNeighboursOf var cspa))

	where
        deleteInconsistentValues :: Assignment -> CSP -> Var -> [Var]-> Bool -> (CSP,Bool)  -- deletes inconsistent values from a var (just loops over it) and controls boolean to return
        deleteInconsistentValues assignments cspa variable [] True = (cspa, True)
        deleteInconsistentValues assignments cspa variable [] False = (cspa, False)
        deleteInconsistentValues assignments cspa variable (var:xs) bool = if deleteInconsistentValuesActual cspa variable var (getDomain var cspa) == [] then deleteInconsistentValues assignments cspa variable xs False else deleteInconsistentValues assignments (setDomain (var, deleteInconsistentValuesActual cspa var (varName $ head $ assignments) (getDomain var cspa)) cspa) variable xs bool

	
        deleteInconsistentValuesActual :: CSP -> Var -> Var -> [Int] -> [Int] --actually deletes inconsistent values from a var
        deleteInconsistentValuesActual cspa _ _ [] = []
        deleteInconsistentValuesActual cspa assigned neighbour (domainvalue:values)	 | (checkConstraints (constraintsOf assigned cspa ++ constraintsOf neighbour cspa) (assign (neighbour, domainvalue) [])) == False = deleteInconsistentValuesActual cspa assigned neighbour values 
									                                                 | otherwise = domainvalue : deleteInconsistentValuesActual cspa assigned neighbour values

        
-- (4.1.ii) Algorithm: 

fcRecursion :: CSP -> Assignment -> (Maybe Assignment, Int)
fcRecursion csp assignment = 
	if (isComplete csp assignment) then (Just assignment,0)
    else findConsistentValue $ getDomain var csp
      where var = firstUnassignedVar assignment csp
            findConsistentValue vals = 
              case vals of  -- recursion over the possible values 
                            -- instead of for-each loop
                []     -> (Nothing,0)
                val:vs -> 
                  if (isConsistentValue csp assignment (var,val)) 
                  then if (isNothing result) 
                       then (ret,nodes+nodes'+1)
                       else (result,nodes+1)
                  else (ret,nodes'+1)
                     where (result,nodes) = fcRecursion (fst $ forwardcheck csp (assign (var,val) assignment) var) $ assign (var,val) assignment
                           (ret,nodes') = findConsistentValue vs


fc :: CSP -> (Maybe Assignment,Int)
fc csp = fcRecursion csp []



-------------------------------------------------
-- (4.2) Minimum Remaining Values (MRV)
-------------------------------------------------


-- (4.2.i) Get next variable according to MRV for the FC algorithm:


--curently this does the MRV for the current state of the CSP, not accounting for the new assignment, you need it to count fot the new assignment


--NEW ONE!--
getMRVVariable :: Assignment -> CSP -> Var  --returns the fist smallest uncdeclared variable in the CSP with the smallest domain
getMRVVariable ass cspa = fst $ last $ sortOn snd (zip (extractUndeclaredVarsFromAssignment ass (cspVars cspa)) (findLenofDomains (extractUndeclaredVarsFromAssignment ass (cspVars cspa)) cspa))
	where
		findLenofDomains :: [Var] -> CSP -> [Int]   --finds the length of the domain of a var
		findLenofDomains [] _ = []
		findLenofDomains (var:vars) csp = length (getDomain var csp) : findLenofDomains vars csp
	
		extractUndeclaredVarsFromAssignment :: Assignment -> [Var] -> [Var]  --finds uncdeclared variables
		extractUndeclaredVarsFromAssignment assignment [] = []
		extractUndeclaredVarsFromAssignment assignment (var:vars) | isAssigned assignment var == False = var : extractUndeclaredVarsFromAssignment assignment vars
									                              | otherwise = extractUndeclaredVarsFromAssignment assignment vars



-- (4.2.ii) FC + MRV algorithm

fcMRVRecursion :: CSP -> Assignment -> (Maybe Assignment,Int)
fcMRVRecursion csp assignment = 
	if (isComplete csp assignment) then (Just assignment,0)
    else findConsistentValue $ getDomain var csp
      where var = getMRVVariable assignment csp
            findConsistentValue vals = 
              case vals of  -- recursion over the possible values 
                            -- instead of for-each loop
                []     -> (Nothing,0)
                val:vs -> 
                  if (isConsistentValue csp assignment (var,val)) 
                  then if (isNothing result) 
                       then (ret,nodes+nodes'+1)
                       else (result,nodes+1)
                  else (ret,nodes'+1)
                     where (result,nodes) = (fcMRVRecursion (fst $ forwardcheck csp (assign (var,val) assignment) var) $ assign (var,val) assignment)
                           (ret,nodes') = findConsistentValue vs

fcMRV :: CSP -> (Maybe Assignment,Int)
fcMRV csp = fcMRVRecursion csp []
						   


-------------------------------------------------
-- (4.3) Least Constraining Value (LCV)
-------------------------------------------------


-- (4.3.i) Function that sorts the domain of a variable based on the LCV heuristic.

lcvSort :: CSP -> Assignment -> Var -> [Int]
lcvSort csp assignment var = map snd (sortOn fst $ zip (func csp var) (getDomain var csp))   -- ([forAllNeighbours csp (allNeighboursOf var csp) domainvalue | domainvalue <- getDomain var csp])
	where
		--for all domain values, find how many domain values are consistent in domains of all neighbouring variables for a given domain value
		func :: CSP -> Var -> [Int] 
		func csp var = [forAllNeighbours csp (allNeighboursOf var csp) domainvalue | domainvalue <- getDomain var csp]
	
		--for all neighbours of x: returns how many domain values are consistent in domains of all neighbouring variables for a given domain value
		forAllNeighbours :: CSP -> [Var] -> Int -> Int
		forAllNeighbours _ [] _ = 0
		forAllNeighbours csp (neighbour:ns) domainValue = consistentValuesInDomain csp neighbour (getDomain neighbour csp) domainValue 0 + forAllNeighbours csp ns domainValue

		--for all domain values of 1 neighbour: returns how many domain values are consistent for a given neighbouring variable
		consistentValuesInDomain :: CSP -> Var -> [Int] -> Int -> Int -> Int
		consistentValuesInDomain csp neighbour [] _ counter = counter
		consistentValuesInDomain csp neighbour (domainValueNeighbour:ds) domainValue counter = if isConsistent csp (assign (neighbour,domainValueNeighbour) $ assign (var,domainValue) assignment) then consistentValuesInDomain csp neighbour ds domainValue counter+1 else consistentValuesInDomain csp neighbour ds domainValue counter


																															

-- (4.3.ii) FC + LCV algorithm

fcLCVRecursion :: CSP -> Assignment -> (Maybe Assignment, Int)
fcLCVRecursion csp assignment= 
	if (isComplete csp assignment) then (Just assignment,0)
    else findConsistentValue $ lcvSort csp assignment var
      where var = firstUnassignedVar assignment csp
            findConsistentValue vals = 
              case vals of  -- recursion over the possible values 
                            -- instead of for-each loop
                []     -> (Nothing,0)
                val:vs -> 
                  if (isConsistentValue csp assignment (var,val)) 
                  then if (isNothing result) 
                       then (ret,nodes+nodes'+1)
                       else (result,nodes+1)
                  else (ret,nodes'+1)
                     where (result,nodes) = (fcLCVRecursion (fst $ forwardcheck csp (assign (var,val) assignment) var) $ assign (var,val) assignment)
                           (ret,nodes') = findConsistentValue vs

fcLCV :: CSP -> (Maybe Assignment,Int)
fcLCV csp = fcLCVRecursion csp []				




-- (4.3.iii) FC + MRV + LCV algorithm

fcMRV_LCVRecursion :: CSP -> Assignment -> (Maybe Assignment, Int)
fcMRV_LCVRecursion csp assignment = 
	if (isComplete csp assignment) then (Just assignment,0)
    else findConsistentValue $ lcvSort csp assignment var
      where var = getMRVVariable assignment csp
            findConsistentValue vals = 
              case vals of  -- recursion over the possible values 
                            -- instead of for-each loop
                []     -> (Nothing,0)
                val:vs -> 
                  if (isConsistentValue csp assignment (var,val)) 
                  then if (isNothing result) 
                       then (ret,nodes+nodes'+1)
                       else (result,nodes+1)
                  else (ret,nodes'+1)
                     where (result,nodes) = (fcMRV_LCVRecursion (fst $ forwardcheck csp (assign (var,val) assignment) var) $ assign (var,val) assignment)
                           (ret,nodes') = findConsistentValue vs



fcMRV_LCV :: CSP -> (Maybe Assignment,Int)
fcMRV_LCV csp = fcMRV_LCVRecursion csp []						   



-------------------------------------------------
-- (5) Evaluation
-------------------------------------------------
{-
  (5.ii) Table:

----------+--------+--------+--------+---------+----------+---------+-----------+
          |   BT     |   FC     | FC+MRV     | FC+LCV   |FC+MRV+LCV|   AC3     |AC3+MRV+LCV|
----------+--------+--------+--------+---------+----------+---------+-----------+
ausCsp    |   32     |   37     |    13     |   38      |    21    |   37    |           |
mapCsp    |  1176    |  1176    |    59     |  4486     |          |  1176   |           |
ms3x3Csp  |  3654    |  3654    |   3654    |  3690     |          |3654     |xxxxxxxxxxx|
8-Queens  |        |        |        |         |          |         |           |
12-Queens |        |        |        |         |          |         |           |
----------+--------+--------+--------+---------+----------+---------+-----------+

  (5.iii - 5.iv) Report:

- Your report must be no longer than one A4 page for the first four algorithms
  and another maximum half page for AC3 and AC3+MRV+LCV.
- Write your report starting here. -
-------------------------------------------------
As more features are added to the basic BT search, the number of nodes visited to find a complete solution decrease.
For example, the number of nodes needed was 32 for BT ausCsp, but 13 for FC+MRV ausCsp

These improvements were expected, since the MRV heuristic, by assigning the most constrained values first, decreases branching,
decreasing the number of nodes that need to be visited to find a complete and consistent solution. The LCV heuristic, by picking the 
least constraining value, i.e. the value which restricts the domain of its neighbours the least, preserves choices, allowing the algorithm 
to visit fewer nodes in the process of finding a complete and consistent solution.

BT vs FC: The BT and FC algorithms gave similar results
FC vs FC MRV: The FC MRV gave better results due to the fact that by decreasing branching, it has to check less nodes.
FC vs FC LCV: While my implementation of the LCV algorithm did not yield better results than the FC, possibly owing to some fault in the implementation,
              normally, the FC LCV algorithm should yield better results than FC alone since by picking the domain value which least reduces the domain of other variables in a CSP,
			  since it gives maximum flexibility in subsequent variable assignments
FC MRV vs FC LCV: While my implementation of the LCV algorithm is faulty, the FC MRV algorithm should indeed have better results than the FC LCV algorithm since by decreasing branching, the MRV
                  algorithm has a direct impact on the max number of nodes visitable, decreasing the amount of nodes visited. However, the LCV algorithm does not have such a drastic impact on the number of nodes.
FC MRV vs FC MRV LCV: The FC MRV LCV should yield better results than FC MRV alone.


-------------------------------------------------
- End of report-
-}


-------------------------------------------------
-- (6) Arc Consistency
-------------------------------------------------


-- (6.i) AC-3 constraint propagation

revise :: CSP -> Var -> Var -> (CSP,Bool)
revise csp i j = func csp i j (getDomain i csp) (getDomain j csp) (constraintsOf i csp ++ constraintsOf j csp) False
	where
		func :: CSP -> Var -> Var -> Domain -> Domain -> [Constraint] -> Bool -> (CSP,Bool)   --actual heart of the revise func. does same thing as revise, just takes in more arguments
		func csp i j [] _ constraints bool = (csp, bool)
		func csp i j (x:xs) [] constraints bool = func (delDomainVal (i,x) csp) i j xs (getDomain j csp) constraints True
		func csp i j (x:xs) (y:ys) constraints bool = do 
			if checkConstraints (constraints) (assign (j,y) $ assign (i,x) [])
			then func csp i j xs (y:ys) constraints bool
			else func csp i j (x:xs) ys constraints bool
	
	
-- (6.ii) AC-3 constraint propagation

ac3Check :: CSP -> [(Var,Var)] -> (CSP,Bool)
ac3Check csp [] = (csp,True)
ac3Check csp (pair:pairs) = if snd (revise csp (fst $ pair) (snd $ pair)) == True
	then if (length $ getDomain (fst pair) csp) == 0 
		then (csp,False) 
		else ac3Check csp (pairs ++ map (\k -> (k,fst pair)) (delete (snd $ pair) (allNeighboursOf (fst $ pair) csp)))
	else (csp,True)

		

-- (6.iii) AC-3 algorithm

ac3Recursion :: CSP -> Assignment -> (Maybe Assignment, Int)
ac3Recursion csp assignment = 
	if (isComplete csp assignment) then (Just assignment,0)
    else findConsistentValue $ getDomain var (fst $ ac3Check csp (getPairs (concat (map scope (cspConstraints csp)))))
      where var = firstUnassignedVar assignment csp
            findConsistentValue vals = 
              case vals of  -- recursion over the possible values 
                            -- instead of for-each loop
                []     -> (Nothing,0)
                val:vs -> 
                  if (isConsistentValue csp assignment (var,val)) 
                  then if (isNothing result) 
                       then (ret,nodes+nodes'+1)
                       else (result,nodes+1)
                  else (ret,nodes'+1)
                     where (result,nodes) = ac3Recursion csp (assign (var,val) assignment)
                           (ret,nodes') = findConsistentValue vs
			
getPairs :: [Var] -> [(Var,Var)]  --makes pairs out of given variables
getPairs [] = []	
getPairs (var:vars) = map ((,) var) vars ++ getPairs vars 


ac3 :: CSP -> (Maybe Assignment,Int)
ac3 csp = ac3Recursion csp []



-- (6.iv) AC-3 algorithm + MRV heuristic + LCV heuristic

ac3MRV_LCVRecursion :: CSP -> Assignment -> (Maybe Assignment, Int)
ac3MRV_LCVRecursion csp assignment = 
	if (isComplete csp assignment) then (Just assignment,0)
    else findConsistentValue $ lcvSort (fst $ ac3Check csp (getPairs (concat (map scope (cspConstraints csp))))) assignment var
      where var = getMRVVariable assignment csp
            findConsistentValue vals = 
              case vals of  -- recursion over the possible values 
                            -- instead of for-each loop
                []     -> (Nothing,0)
                val:vs -> 
                  if (isConsistentValue csp assignment (var,val)) 
                  then if (isNothing result) 
                       then (ret,nodes+nodes'+1)
                       else (result,nodes+1)
                  else (ret,nodes'+1)
                     where (result,nodes) = ac3Recursion csp $ assign (var,val) assignment
                           (ret,nodes') = findConsistentValue vs


ac3MRV_LCV :: CSP -> (Maybe Assignment,Int)
ac3MRV_LCV csp = ac3MRV_LCVRecursion csp []

-------------------------------------------------