module Nim

import Data.Maybe
import Data.Fin
import Data.List
import Data.List1
import Data.SortedMap
import Data.SortedSet
import Data.Strings
import Data.Vect
import System
import System.File

import Pfsm
import Pfsm.Analyser
import Pfsm.Checker
import Pfsm.Data
import Pfsm.Matrix
import Pfsm.Nim
import Pfsm.Parser

indentDelta : Nat
indentDelta = 2

eventWithGuards : List Trigger -> List (Event, List TestExpression)
eventWithGuards
  = eventWithGuards' empty
  where
    eventWithGuards' : SortedMap Event (List TestExpression) -> List Trigger -> List (Event, List TestExpression)
    eventWithGuards' acc []                                 = toList acc
    eventWithGuards' acc ((MkTrigger _ e (Just g) _) :: ts) = case lookup e acc of
                                                                   Just gs => eventWithGuards' (insert e (nub (g :: gs)) acc) ts
                                                                   Nothing => eventWithGuards' (insert e [g] acc) ts
    eventWithGuards' acc ((MkTrigger _ e Nothing _) :: ts)  = case lookup e acc of
                                                                         Just gs => eventWithGuards' acc ts
                                                                         Nothing => eventWithGuards' (insert e [] acc) ts

eventGuardTags : List1 Transition -> List String
eventGuardTags trans
  = let triggers = flatten $ List1.toList $ (map (\x => List1.toList x.triggers) trans) in
        eventGuardTags' (eventWithGuards triggers) []
  where
    eventGuardTags' : List (Event, List TestExpression) -> List String -> List String
    eventGuardTags' []              acc = acc
    eventGuardTags' ((e, gs) :: xs) acc = eventGuardTags' xs $ acc ++ ((show e) :: (map (\x => (show e) ++ (show x)) gs))

updateStateMatrix : {r, c: Nat} -> Maybe Nat -> Maybe Nat -> Maybe Int -> Matrix r c Int -> Matrix r c Int
updateStateMatrix {r} {c} (Just row) (Just col) (Just v) m = let rowMaybe = natToFin row r
                                                                 colMaybe = natToFin col c in
                                                                 case (rowMaybe, colMaybe) of
                                                                      (Just row', Just col') => replaceAt row' col' v m
                                                                      _ => m
updateStateMatrix         _          _          _        m = m

stateMatrix : (states: List1 State) -> (eventGuards: List String) -> List1 Transition -> Matrix (1 + (length states)) (length eventGuards) Int
stateMatrix ss egts ts
  = let matrix = create (1 + (length ss)) (length egts) (the Int 0) in
        foldl (\acc, x => let s = List1.index x.src ss
                              d = List1.index x.dst ss
                              v = Just (-) <*> map cast d <*> map cast s in
                              foldl (\acc', y => updateMatrix egts s v y acc') acc x.triggers
                              ) matrix ts
  where
    updateMatrix : {row: Nat} -> (eventGuards: List String) -> Maybe Nat -> Maybe Int -> Trigger -> Matrix row (length eventGuards) Int -> Matrix row (length eventGuards) Int
    updateMatrix egts s v (MkTrigger _ evt Nothing _)  m = let e = Data.List.index (show evt) egts in
                                                               updateStateMatrix (map (+ 1) s) e v m
    updateMatrix egts s v (MkTrigger _ evt (Just g) _) m = let e = Data.List.index ((show evt) ++ show g) egts in
                                                               updateStateMatrix (map (+ 1) s) e v m

actionTags : List1 Transition -> List String
actionTags trans
  = nub $ map (foldl (\acc, x => acc ++ (show x)) "") $ nub $ actionsOfTransitions trans

transitionActionMatrix : (states: List1 State) -> (eventGuards: List String) -> List1 Transition -> List String -> Matrix (1 + length states) (length eventGuards) Int
transitionActionMatrix ss egts ts ats
  = let matrix = create (1 + (length ss)) (length egts) (the Int 0) in
        foldl (\acc, x => let s = map (+ 1) $ List1.index x.src ss in
                              foldl (\acc', y => calcAction egts ats s y acc') acc x.triggers
                              ) matrix ts
  where
    calcAction : {r: Nat} -> (eventGuards: List String) -> List String -> Maybe Nat -> Trigger -> Matrix r (length eventGuards) Int -> Matrix r (length eventGuards) Int
    calcAction egts ats s (MkTrigger _ e _        Nothing)   m = m
    calcAction egts ats s (MkTrigger _ e Nothing  (Just as)) m = let c = Data.List.index (show e) egts
                                                                     v = map ((+ 1) . cast . natToInteger) $ Data.List.index (foldl (\acc, x => acc ++ (show x)) "" as) ats in
                                                                     updateStateMatrix s c v m
    calcAction egts ats s (MkTrigger _ e (Just g) (Just as)) m = let c = Data.List.index ((show e) ++ (show g)) egts
                                                                     v = map ((+ 1) . cast . natToInteger) $ Data.List.index (foldl (\acc, x => acc ++ (show x)) "" as) ats in
                                                                     updateStateMatrix s c v m

stateActionMatrix : (State -> State -> Maybe (List Action)) -> (states : List1 State) -> List String -> Matrix (1 + length states) (1 + length states) Int
stateActionMatrix f ss tags
  = calcActions f ss tags $ create (1 + length ss) (1 + length ss) 0
  where
    calcActionVector : {dim : Nat} -> (State -> State -> Maybe (List Action)) -> Nat -> State -> List1 State -> List String -> Matrix dim dim Int -> Matrix dim dim Int
    calcActionVector f si s ss tags m = foldl (\acc, x => case f s x of
                                                               Just as => if s == x
                                                                             then acc
                                                                             else updateStateMatrix (Just (si + 1)) (map (+ 1) (List1.index x ss)) (map ((+ 1) . cast . natToInteger) (Data.List.index (show as) tags)) acc
                                                               Nothing => acc) m ss

    calcActions : (State -> State -> Maybe (List Action)) -> (states: List1 State) -> List String -> Matrix (1 + length states) (1 + length states) Int -> Matrix (1 + length states) (1 + length states) Int
    calcActions f states tags m = foldl (\acc, (i, s) => calcActionVector f i s states tags acc) m (List1.enumerate states)

intMatrixToNim : {r, c: Nat} -> (Int -> String) -> Matrix r c Int -> String
intMatrixToNim {r} {c} f (MkMatrix xs) = Data.Vect.join ",\n" (map (\x => (indent indentDelta) ++ x) (map (\x => Data.Vect.join ", " (map f x)) xs))

%hide Data.Vect.(::)

toNim : Fsm -> String
toNim fsm
  = List.join "\n\n" [ generateImports
                     , generateTypes fsm
                     , generateActions fsm
                     , generateMatrixs fsm
                     , generateInternalExec fsm
                     , generateEvents fsm
                     , generateInitModel fsm
                     ]
  where
    generateImports : String
    generateImports
      = List.join "\n" $ map ("import " ++) [ "options"
                                            , "strtabs"
                                            , "tables"
                                            ]

    generateTypes : Fsm -> String
    generateTypes fsm
      = let pre = camelize fsm.name
            env = rootEnv fsm
            rks = liftRecords fsm.model
            oas = liftOutputActions fsm.states fsm.transitions
            ges = nub $ filter applicationExpressionFilter $ flatten $ map expressionsOfTestExpression $ flatten $ map guardsOfTransition $ List1.toList fsm.transitions
            ads = generateActionDelegates indentDelta pre env fsm.states fsm.transitions
            ods = generateOutputDelegates indentDelta pre env oas
            gds = generateGuardDelegates indentDelta pre env ges in
            List.join "\n" $ List.filter nonblank [ "type"
                                                  , generateRecords indentDelta rks
                                                  , generateModel indentDelta pre (filter (\(n, _, _) => n /= "state") fsm.model)
                                                  , generateStates indentDelta pre fsm.states
                                                  , ads
                                                  , ods
                                                  , gds
                                                  , generateStateMachine indentDelta pre (0 /= length ads) (0 /= length ods) (0 /= length gds)
                                                  , generateTransitionActionType indentDelta pre fsm.events
                                                  , generateStateActionType indentDelta pre
                                                  ]
      where
        generateAttribute : Nat -> Parameter -> String
        generateAttribute idt (n, t, _)
          = (indent idt) ++ (toNimName n) ++ "*: " ++ (toNimType t)

        generateRecords : Nat -> List Tipe -> String
        generateRecords idt ts
            = join "\n" $ filter nonblank $ map (generateRecord idt) ts
          where
            generateRecord : Nat -> Tipe -> String
            generateRecord idt (TRecord n ps) = List.join "\n" [ (indent idt) ++ (camelize n) ++ "* = ref object of RootObj"
                                                               , join "\n" $ map (generateAttribute (idt + indentDelta)) ps
                                                               ]
            generateRecord idt _              = ""

        generateModel : Nat -> String -> List Parameter -> String
        generateModel idt pre as
          = List.join "\n" [ (indent idt) ++ pre ++ "Model* = ref object of RootObj"
                           , List1.join "\n" $ map (generateAttribute (idt + indentDelta)) (("state", (TPrimType PTInt), Nothing) :: as)
                           ]

        generateStates : Nat -> String -> List1 State -> String
        generateStates idt pre ss
          = List.join "\n" [ (indent idt) ++ pre ++ "State* = enum"
                           , List1.join ",\n" $ map (\(i, x) => generateState (idt + indentDelta) i x) (enumerate ss)
                           ]
          where
            generateState : Nat -> Nat -> State -> String
            generateState idt idx (MkState n _ _ _)
              = (indent idt) ++ ((toNimName . camelize) n) ++ " = " ++ (show (idx + 1))

        generateActionDelegates : Nat -> String -> SortedMap Expression Tipe -> List1 State -> List1 Transition -> String
        generateActionDelegates idt pre env states transitions
          = let ats = actionTypeOfStates env states SortedMap.empty
                ats' = actionTypeOfTransitions env transitions ats
                ats'' = SortedMap.toList ats'
                head = (indent idt) ++ pre ++ "ActionDelegate* = ref object of RootObj"
                body = join "\n" (map (\(n, t) => (generateActionDelegate (idt + indentDelta) n t)) ats'') in
                if length ats'' > Z
                   then List.join "\n" [head, body]
                   else ""
          where
            generateActionDelegate: Nat -> Name -> Tipe -> String
            generateActionDelegate idt n t
              = (indent idt) ++ (toNimFuncName n) ++ "*: " ++ (toNimType t)

            applicationExpressionTypeOfAssigmentAction : SortedMap Expression Tipe -> SortedMap String Tipe -> Action -> SortedMap String Tipe
            applicationExpressionTypeOfAssigmentAction env acc (AssignmentAction l r@(ApplicationExpression n _)) = insert n (fromMaybe TUnit (fixTypeOfApplicationExpression env (inferType env r) (inferType env l))) acc
            applicationExpressionTypeOfAssigmentAction env acc _                                                  = acc

            applicationExpressionTypeOfOutputAction : SortedMap Expression Tipe -> SortedMap String Tipe -> Action -> SortedMap String Tipe
            applicationExpressionTypeOfOutputAction env acc (OutputAction (MkPort _ pt) es)
              = iterateExpression env acc pt es
              where
                iterateExpression : SortedMap Expression Tipe -> SortedMap String Tipe -> Tipe -> List Expression -> SortedMap String Tipe
                iterateExpression env acc TUnit            (e :: _)                              = acc
                iterateExpression env acc (TArrow src dst) (e@(ApplicationExpression n _) :: es) = iterateExpression env (insert n (fromMaybe TUnit (fixTypeOfApplicationExpression env (inferType env e) (Just src))) acc) dst es
                iterateExpression env acc (TArrow src dst) (e :: es)                             = iterateExpression env acc dst es
                iterateExpression env acc _                _                                     = acc
            applicationExpressionTypeOfOutputAction env acc _
              = acc

            actionTypeOfStates : SortedMap Expression Tipe -> List1 State -> SortedMap String Tipe -> SortedMap String Tipe
            actionTypeOfStates env states acc
              = let actions = flatten $ map liftActionsFromState $ List1.toList states
                    ats = foldl (applicationExpressionTypeOfAssigmentAction env) acc actions
                    ats' = foldl (applicationExpressionTypeOfOutputAction env) ats actions in
                    ats'

            actionTypeOfTransitions : SortedMap Expression Tipe -> List1 Transition -> SortedMap String Tipe -> SortedMap String Tipe
            actionTypeOfTransitions env transitions acc
              = foldl (actionTypeOfTransition env) acc transitions
              where
                actionTypeOfTrigger : SortedMap Expression Tipe -> SortedMap String Tipe -> Trigger -> SortedMap String Tipe
                actionTypeOfTrigger env acc (MkTrigger _ (MkEvent _ ps _) _ (Just as))
                  = let env' = foldl (\acc, (n, t, _) => insert (IdentifyExpression ("@" ++ n)) t acc) env ps
                        ats = foldl (applicationExpressionTypeOfAssigmentAction env') acc as
                        ats' = foldl (applicationExpressionTypeOfOutputAction env') ats as in
                        ats'
                actionTypeOfTrigger env acc (MkTrigger _ (MkEvent _ ps _) _ Nothing)
                  = acc

                actionTypeOfTransition : SortedMap Expression Tipe -> SortedMap String Tipe -> Transition -> SortedMap String Tipe
                actionTypeOfTransition env acc (MkTransition _ _ ts)
                  = foldl (actionTypeOfTrigger env) acc ts

        generateOutputDelegates : Nat -> String -> SortedMap Expression Tipe -> List Action -> String
        generateOutputDelegates idt pre env as
          = let oas = filter outputActionFilter as
                pts = nub $ fromMaybe [] $ liftMaybeList $ map liftPort oas
--              oes = (SortedMap.toList . (foldl (\acc, x => expressionOfOutputAction x acc) SortedMap.empty)) as
                fps = map (\(MkPort n t) => (n, TArrow (TRecord (pre ++ "Model") []) t)) pts
                head = (indent idt) ++ pre ++ "OutputDelegate* = ref object of RootObj"
                body = join "\n" (map (\(n, t) => (generateOutputDelegate (idt + indentDelta) n t)) fps) in
                if length fps > 0
                   then List.join "\n" [head, body]
                   else ""
          where
            liftPort : Action -> Maybe Port
            liftPort (OutputAction p _) = Just p
            liftPort _                  = Nothing

            generateOutputDelegate : Nat -> Name -> Tipe -> String
            generateOutputDelegate idt n t = (indent idt) ++ (toNimName n) ++ "*: " ++ (toNimType t)

        generateGuardDelegates : Nat -> String -> SortedMap Expression Tipe -> List Expression -> String
        generateGuardDelegates idt pre env ges
          = let fps = foldl (\acc, x => case x of Just x' => x' :: acc; Nothing => acc) (the (List (Name, Tipe)) []) $ map (inferTypeOfExpressions env (TRecord (pre ++ "Model") [])) ges
                head = (indent idt) ++ pre ++ "GuardDelegate* = ref object of RootObj"
                body = join "\n" (map (\(n, t) => (generateGuardDelegate (idt + indentDelta) n t)) fps) in
                if length fps > Z
                   then List.join "\n" [head, body]
                   else ""
          where
            generateGuardDelegate : Nat -> Name -> Tipe -> String
            generateGuardDelegate idt n t = (indent idt) ++ (toNimName n) ++ "*: " ++ (toNimType t)

            inferTypeOfExpressions : SortedMap Expression Tipe -> Tipe -> Expression -> Maybe (Name, Tipe)
            inferTypeOfExpressions env firstArgType r@(ApplicationExpression n _) = case fixTypeOfApplicationExpression env (inferType env r) (Just (TPrimType PTBool)) of
                                                                                         Just (TArrow TUnit (TPrimType PTBool)) => Just (n, (TArrow firstArgType (TPrimType PTBool)))
                                                                                         Just a => Just (n, (TArrow firstArgType a))
                                                                                         Nothing => Nothing
            inferTypeOfExpressions _   _            _                             = Nothing

        generateStateMachine : Nat -> String -> Bool -> Bool -> Bool -> String
        generateStateMachine idt pre ads ods gds
          = let head = (indent idt) ++ pre ++ "StateMachine* = ref object of RootObj"
                ad = if ads then (indent (idt + indentDelta)) ++ "action_delegate*: " ++ pre ++ "ActionDelegate" else ""
                od = if ods then (indent (idt + indentDelta)) ++ "output_delegate*: " ++ pre ++ "OutputDelegate" else ""
                gd = if gds then (indent (idt + indentDelta)) ++ "guard_delegate*: " ++ pre ++ "GuardDelegate" else ""
                body = List.join "\n" (List.filter (\x => 0 /= length x) [ad, od, gd]) in
                List.join "\n" [head, body]

        generateTransitionActionType : Nat -> String -> List1 Event -> String
        generateTransitionActionType idt pre es
          = let params = parametersOfEvents es
                paramcodes = foldl (\acc, (n, t, _) => acc ++ ", " ++ (toNimName n) ++ "_opt: Option[" ++ (toNimType t) ++ "]" ) ("fsm: " ++ pre ++ "StateMachine, model: " ++ pre ++ "Model") params in
                (indent idt) ++ "TransitionActionFunc = proc (" ++ paramcodes ++ "): " ++ pre ++ "Model"

        generateStateActionType : Nat -> String -> String
        generateStateActionType idt pre = (indent idt) ++ "StateActionFunc = proc (fsm: " ++ pre ++ "StateMachine, model: " ++ pre ++ "Model): " ++ pre ++ "Model"

    generateMatrixs : Fsm -> String
    generateMatrixs fsm
      = let ss   = fsm.states
            ts   = fsm.transitions
            egts = eventGuardTags ts
            ents = map show $ nub $ actionsOfStates (.onEnter) ss
            exts = map show $ nub $ actionsOfStates (.onExit) ss
            ats  = actionTags ts in
            List.join "\n\n" [ generateTransitionStateMatrix ss egts ts
                             , generateTransitionActionMatrix ss egts ts ats
                             , generateStateOnEnterMatrix ss ents
                             , generateStateOnExitMatrix ss exts
                             ]
      where

        generateTransitionStateMatrix : List1 State -> List String -> List1 Transition -> String
        generateTransitionStateMatrix ss egts ts
          = let matrix = stateMatrix ss egts ts
                code = intMatrixToNim show matrix in
                "const transition_states: array[0.." ++ (show (cast (((length ss) + 1) * (length egts)) - 1)) ++ ", int] = [\n" ++ code ++ "\n]"

        generateTransitionActionMatrix : List1 State -> List String -> List1 Transition -> List String -> String
        generateTransitionActionMatrix ss egts ts ats
          = let matrix = transitionActionMatrix ss egts ts ats
                code = intMatrixToNim (\x => "TransitionActionFunc(transition_action" ++ (show x) ++ ")") matrix in
                "const transition_actions: array[0.." ++ (show (cast (((length ss) + 1) * (length egts)) - 1)) ++ ", TransitionActionFunc] = [\n" ++ code ++ "\n]"

        generateStateOnEnterMatrix : List1 State -> List String -> String
        generateStateOnEnterMatrix ss tags
          = let matrix = stateActionMatrix (\s, d => d.onEnter) ss tags
                code = intMatrixToNim (\x => "StateActionFunc(on_enter_action" ++ (show x) ++ ")") matrix in
                "const on_enter_actions: array[0.." ++ (show (cast (((length ss) + 1) * ((length ss) + 1)) - 1)) ++ ", StateActionFunc] = [\n" ++ code ++ "\n]"

        generateStateOnExitMatrix : List1 State -> List String -> String
        generateStateOnExitMatrix ss tags
          = let matrix = stateActionMatrix (\s, d => s.onExit) ss tags
                code = intMatrixToNim (\x => "StateActionFunc(on_exit_action" ++ (show x) ++ ")") matrix in
                "const on_exit_actions: array[0.." ++ (show (cast (((length ss) + 1) * ((length ss) + 1)) - 1)) ++ ", StateActionFunc] = [\n" ++ code ++ "\n]"

    generateAction : String -> String -> String -> (Nat, List Action) -> String
    generateAction pre funpre paramcodes (idx, acts)
      = let signature = "proc " ++ funpre ++ "_action" ++ (show idx) ++ "(" ++ paramcodes ++ "): " ++ pre ++ "Model ="
            usedArgs = liftUsedArgumentsFromActions acts
            actionsCode = generateActionsCode acts
            body = generateActionsBody indentDelta pre (reverse actionsCode) usedArgs in
            signature ++ "\n" ++ body
      where
        liftUsedArgumentsFromActions : List Action -> List Name
        liftUsedArgumentsFromActions acts
          = SortedSet.toList $ liftUsedArgumentsFromActions' acts SortedSet.empty
          where
            liftUsedArgumentsFromExpression : Expression -> List Name
            liftUsedArgumentsFromExpression (IdentifyExpression s)       = if isPrefixOf "@" s
                                                                              then []
                                                                              else [s]
            liftUsedArgumentsFromExpression (ApplicationExpression _ ss) = concat $ map liftUsedArgumentsFromExpression ss
            liftUsedArgumentsFromExpression _                            = []

            liftUsedArgumentsFromActions' : List Action -> SortedSet Name -> SortedSet Name
            liftUsedArgumentsFromActions' []                             acc = acc
            liftUsedArgumentsFromActions' ((AssignmentAction _ e) :: xs) acc = liftUsedArgumentsFromActions' xs $ foldl (\a, x => insert x a) acc $ liftUsedArgumentsFromExpression e
            liftUsedArgumentsFromActions' ((OutputAction _ es) :: xs)    acc = liftUsedArgumentsFromActions' xs $ foldl (\acc', x => foldl (\a, y => insert y a) acc' x) acc $ map (liftUsedArgumentsFromExpression) es
            liftUsedArgumentsFromActions' (_ :: xs)                      acc = liftUsedArgumentsFromActions' xs acc

        generateActionsBody : Nat -> String -> List String -> List Name -> String
        generateActionsBody idt pre bodies ns
          = generateActionsBody' idt pre bodies ns "" "" []
          where
            generateActionsBody' : Nat -> String -> List String -> List Name -> String -> String -> List String -> String
            generateActionsBody' idt pre bodies []        acc1 acc2 args = acc1 ++ (join "\n" (map (\x => (indent idt) ++ x) (args ++ bodies ++ ["result = model\n"]))) ++ acc2
            generateActionsBody' idt pre bodies (n :: ns) acc1 acc2 args = generateActionsBody' (idt + indentDelta) pre bodies ns (acc1 ++ (indent idt) ++ "if " ++ (toNimName n) ++ "_opt.isSome:\n") ((indent idt) ++ "else:\n" ++ (indent (idt + indentDelta)) ++ "result = model\n" ++ acc2) (("let " ++ (toNimName n) ++ " = " ++ (toNimName n) ++ "_opt.get") :: args)

        generateActionsCode : List Action -> List String
        generateActionsCode
          = generateActionsCode' []
          where
            generateActionsCode' : List String -> List Action -> List String
            generateActionsCode' acc []                             = acc
            generateActionsCode' acc ((AssignmentAction l r) :: xs) = generateActionsCode' (((toNimModelAttribute (show l)) ++ " = " ++ (toNimExpression "fsm.action_delegate" r)) :: acc) xs
            generateActionsCode' acc ((OutputAction p es) :: xs)    = generateActionsCode' (("fsm.output_delegate." ++ toNimName(p.name) ++ "(" ++ (List.join ", " (map (toNimExpression "fsm.action_delegate") ((IdentifyExpression "model") :: es))) ++ ")") :: acc) xs
            generateActionsCode' acc (_ :: xs)                      = generateActionsCode' acc xs

    generateTransitionActions : String -> List1 State -> List1 Event -> List1 Transition -> String
    generateTransitionActions pre ss es ts
      = let as = nub $ actionsOfTransitions ts
            params = parametersOfEvents es
            paramcodes = foldl (\acc, (n, t, _) => acc ++ ", " ++ (toNimName n) ++ "_opt: Option[" ++ (toNimType t) ++ "]" ) ("fsm: " ++ pre ++ "StateMachine, model: " ++ pre ++ "Model") params
            funcs = map (generateAction pre "transition" paramcodes) (Data.List.enumerate ([] :: as)) in
            join "\n" funcs

    generateStateActions : (State -> Maybe (List Action)) -> String -> String -> List1 State -> String
    generateStateActions f pre funpre ss
      = let as = nub $ actionsOfStates f ss
            funcs = map (generateAction pre funpre ("fsm: " ++ pre ++ "StateMachine, model: " ++ pre ++ "Model")) (Data.List.enumerate ([] :: as)) in
            join "\n" funcs

    generateActions : Fsm -> String
    generateActions fsm
      = let pre = camelize fsm.name
            ss  = fsm.states
            es  = fsm.events
            ts  = fsm.transitions in
            List.join "\n" [ generateTransitionActions pre ss es ts
                           , generateStateActions (.onEnter) pre "on_enter" ss
                           , generateStateActions (.onExit) pre "on_exit" ss
                           ]

    generateEvents : Fsm -> String
    generateEvents fsm
      = let pre    = camelize fsm.name
            es     = fsm.events
            ts     = flatten $ List1.toList $ map (List1.toList . (.triggers)) fsm.transitions
            egts   = eventGuardTags fsm.transitions
            params = parametersOfEvents es in
            join "\n\n" $ map (\(e, gs) => generateEvent pre e gs egts params) $ eventWithGuards ts
      where
        generateEventBody : Nat -> List String -> Event -> List TestExpression -> String
        generateEventBody idt egts e []           = (indent idt) ++ "let idx = (model.state * " ++ (show (length egts)) ++ ") + " ++ (foldr (\x, acc => show x) "0" (index (show e) egts))
        generateEventBody idt egts e gs@(x :: xs) = (indent idt) ++ "var idx = 0\n" ++ (((join "\n") . reverse) $ generateEventBody' idt egts e gs True [])
          where
            generateEventBody' : Nat -> List String -> Event -> List TestExpression -> Bool -> List String -> List String
            generateEventBody' idt egts e []        _       acc = ((indent idt) ++ "else:\n" ++ (indent (idt + indentDelta)) ++ "idx = (model.state * " ++ (show (length egts)) ++ ") + " ++ (foldr (\x, acc => show x) "0" (index (show e) egts))) :: acc
            generateEventBody' idt egts e (x :: xs) isFirst acc = let ifcode = if isFirst then "if " else "elif "
                                                                      code = (indent idt) ++ ifcode ++ (toNimTestExpression "fsm.guard_delegate" x) ++ ":\n" ++ (indent (idt + indentDelta)) ++ "idx = (model.state * " ++ (show (length egts)) ++ ") + " ++ (foldr (\x, acc => show x) "0" (index ((show e) ++ (show x)) egts)) in
                                                                      generateEventBody' idt egts e xs False $ code :: acc

        generateEvent : String -> Event -> List TestExpression -> List String -> List Parameter -> String
        generateEvent pre e gs egts ps
          = let eparams = e.params
                paramcodes = List.join ", " $ map (\(n, t, _) => (toNimName n) ++ ": " ++ (toNimType t)) (("fsm", TRecord (pre ++ "StateMachine") [], Nothing) :: (("model", TRecord (pre ++ "Model") [], Nothing) :: eparams))
                args = generateArguments eparams ps []
                signature = "proc " ++ (toNimName e.name) ++ "*" ++ "(" ++ paramcodes ++ "): " ++ pre ++ "Model ="
                body = List.join "\n" [ generateEventBody indentDelta egts e gs
                                      , (indent indentDelta) ++ (foldl (\acc, x => acc ++ ", " ++ x) "result = exec(fsm, model, idx" args) ++ ")"
                                      ] in
                signature ++ "\n" ++ body
          where
            generateArguments : List Parameter -> List Parameter -> List String -> List String
            generateArguments eps [] acc = reverse acc
            generateArguments eps (a@(n, t, _) :: xs) acc = if elemBy (==) a eps
                                                               then generateArguments eps xs $ ("some(" ++ (toNimName n) ++ ")") :: acc
                                                               else generateArguments eps xs $ ("none(" ++ (toNimType t) ++ ")") :: acc

    generateInternalExec : Fsm -> String
    generateInternalExec fsm
      = let pre = camelize fsm.name
            statelen = length fsm.states
            es  = fsm.events
            params = parametersOfEvents es
            paramcodes = foldl (\acc, (n, t, _) => acc ++ ", " ++ (toNimName n) ++ "_opt: Option[" ++ (toNimType t) ++ "]") ("fsm: " ++ pre ++ "StateMachine, model: " ++ pre ++ "Model, idx: int") params
            argcodes = foldl (\acc, (n, t, _) => acc ++ ", " ++ (toNimName n) ++ "_opt") (the String "fsm, model1") params in
            List.join "\n" [ "proc exec(" ++ paramcodes ++ "): " ++ pre ++ "Model ="
                           , (indent indentDelta) ++ "let"
                           , (indent (indentDelta * 2)) ++ "oldstate = model.state"
                           , (indent (indentDelta * 2)) ++ "newstate = model.state + transition_states[idx]"
                           , (indent (indentDelta * 2)) ++ "model1 = on_exit_actions[oldstate * " ++ (show (statelen + 1)) ++ " + newstate](fsm, model)"
                           , (indent (indentDelta * 2)) ++ "model2 = transition_actions[idx](" ++ argcodes ++ ")"
                           , (indent (indentDelta * 2)) ++ "model3 = on_enter_actions[oldstate * " ++ (show (statelen + 1)) ++ " + newstate](fsm, model2)"
                           , (indent indentDelta) ++ "model3.state = newstate"
                           , (indent indentDelta) ++ "result = model3"
                           ]

    generateInitModel : Fsm -> String
    generateInitModel fsm
      = let pre = camelize fsm.name
            defaultStateStr = "ord(" ++ pre ++ "State." ++ (camelize fsm.states.head.name) ++ ")"
            startStateStr = fromMaybe defaultStateStr (map (\x => "ord(" ++ pre ++ "State." ++ (camelize x.name) ++ ")") (startState fsm)) in
            List.join "\n" [ "proc init" ++ pre ++ "Model*(): " ++ pre ++ "Model ="
                           , (indent indentDelta) ++ "result = " ++ pre ++ "Model(state: " ++ startStateStr ++ ")"
                           ]

doWork : String -> IO ()
doWork src
  = do Right fsm <- loadFsmFromFile src
       | Left err => putStrLn err
       putStrLn $ toNim fsm

usage : IO ()
usage
  = putStrLn "Usage: pfsm-to-nim <src>"

main : IO ()
main
  = do
    args <- getArgs
    case args of
         x0 :: x1 :: [] => doWork x1
         _ => usage
