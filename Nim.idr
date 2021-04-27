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

record AppConfig where
  constructor MkAppConfig
  src : String
  ignoreStateAction: Bool

calculateScoreOfExpression : Expression -> Nat
calculateScoreOfExpression (ApplicationExpression _ _)  = 1
calculateScoreOfExpression (BooleanExpression _)        = 0
calculateScoreOfExpression (IdentifyExpression _)       = 0
calculateScoreOfExpression (IntegerLiteralExpression _) = 0
calculateScoreOfExpression (RealLiteralExpression _)    = 0
calculateScoreOfExpression (CharLiteralExpression _)    = 0
calculateScoreOfExpression (StringLiteralExpression _)  = 0

calculateScoreOfTestExpression : TestExpression -> Nat
calculateScoreOfTestExpression (PrimitiveTestExpression e)
  = calculateScoreOfExpression e
calculateScoreOfTestExpression (BinaryTestExpression _ te1 te2)
  = let s1 = calculateScoreOfTestExpression te1
        s2 = calculateScoreOfTestExpression te2 in
        s1 + s2 + 2
calculateScoreOfTestExpression (UnaryTestExpression _ te)
  = let s = calculateScoreOfTestExpression te in
        s + 1
calculateScoreOfTestExpression (CompareExpression _ e1 e2)
  = let s1 = calculateScoreOfExpression e1
        s2 = calculateScoreOfExpression e2 in
        s1 + s2

compareTestExpression : TestExpression -> TestExpression -> Ordering
compareTestExpression a b
  = let a' = calculateScoreOfTestExpression a
        b' = calculateScoreOfTestExpression b in
        compare a' b'

eventWithGuards : List Trigger -> List (Event, List TestExpression)
eventWithGuards
  = eventWithGuards' empty
  where
    eventWithGuards' : SortedMap Event (List TestExpression) -> List Trigger -> List (Event, List TestExpression)
    eventWithGuards' acc []                                 = map (\(e, gs) => (e, sortBy compareTestExpression gs)) (the (List (Event, List TestExpression)) (toList acc))
    eventWithGuards' acc ((MkTrigger _ e (Just g) _) :: ts) = case lookup e acc of
                                                                   Just gs => eventWithGuards' (insert e (nub (g :: gs)) acc) ts
                                                                   Nothing => eventWithGuards' (insert e [g] acc) ts
    eventWithGuards' acc ((MkTrigger _ e Nothing _) :: ts)  = case lookup e acc of
                                                                         Just gs => eventWithGuards' acc ts
                                                                         Nothing => eventWithGuards' (insert e [] acc) ts

eventGuardTags : List1 Transition -> List String
eventGuardTags trans
  = let triggers = flatten $ List1.forget $ (map (\x => List1.forget x.triggers) trans) in
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

stateMatrix : (states: List1 State) -> (eventGuards: List String) -> List1 Transition -> Matrix (length states) (length eventGuards) Int
stateMatrix ss egts ts
  = let matrix = create (length ss) (length egts) (the Int 0)
        matrix' = foldl (\acc, x =>
                    case List1.index x.src ss of
                         Just s => case natToFin s (length ss) of
                                        Just s' => replaceRow s' (Vect.replicate (length egts) (cast s)) acc
                                        Nothing => acc
                         Nothing => acc) matrix ts in
        foldl (\acc, x =>
          let s = List1.index x.src ss
              d = List1.index x.dst ss
              v = map cast d in
              foldl (\acc', y => updateMatrix egts s v y acc') acc x.triggers) matrix' ts
  where
    updateMatrix : {row: Nat} -> (eventGuards: List String) -> Maybe Nat -> Maybe Int -> Trigger -> Matrix row (length eventGuards) Int -> Matrix row (length eventGuards) Int
    updateMatrix egts s v (MkTrigger _ evt Nothing _)  m = let e = Data.List.index (show evt) egts in
                                                               updateStateMatrix s e v m
    updateMatrix egts s v (MkTrigger _ evt (Just g) _) m = let e = Data.List.index ((show evt) ++ show g) egts in
                                                               updateStateMatrix s e v m

actionTags : List1 Transition -> List String
actionTags trans
  = nub $ map (foldl (\acc, x => acc ++ (show x)) "") $ nub $ actionsOfTransitions trans

transitionActionMatrix : (states: List1 State) -> (eventGuards: List String) -> List1 Transition -> List String -> Matrix (length states) (length eventGuards) Int
transitionActionMatrix ss egts ts ats
  = let matrix = create (length ss) (length egts) (the Int 0) in
        foldl (\acc, x => let s = List1.index x.src ss in
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

stateActionMatrix : (State -> State -> Maybe (List Action)) -> (states : List1 State) -> List String -> Matrix (length states) (length states) Int
stateActionMatrix f ss tags
  = calcActions f ss tags $ create (length ss) (length ss) 0
  where
    calcActionVector : {dim : Nat} -> (State -> State -> Maybe (List Action)) -> Nat -> State -> List1 State -> List String -> Matrix dim dim Int -> Matrix dim dim Int
    calcActionVector f si s ss tags m
      = foldl (\acc, x =>
          case f s x of
               Just as => if s == x
                             then acc
                             else updateStateMatrix (Just si) (List1.index x ss) (map ((+ 1) . cast . natToInteger) (Data.List.index (show as) tags)) acc
               Nothing => acc) m ss

    calcActions : (State -> State -> Maybe (List Action)) -> (states: List1 State) -> List String -> Matrix (length states) (length states) Int -> Matrix (length states) (length states) Int
    calcActions f states tags m = foldl (\acc, (i, s) => calcActionVector f i s states tags acc) m (List1.enumerate states)

intMatrixToNim : {r, c: Nat} -> (Int -> String) -> Matrix r c Int -> String
intMatrixToNim {r} {c} f (MkMatrix xs) = Data.Vect.join ",\n" (map (\x => (indent indentDelta) ++ x) (map (\x => Data.Vect.join ", " (map f x)) xs))

%hide Data.Vect.(::)

toNim : AppConfig -> Fsm -> String
toNim conf fsm
  = List.join "\n\n" [ generateImports
                     , generateTypes conf fsm
                     , generateActions conf fsm
                     , generateMatrixs conf fsm
                     , generateInternalExec conf fsm
                     , generateEvents conf fsm
                     , generateInitModel fsm
                     ]
  where
    returnType : Tipe -> Tipe
    returnType (TArrow _ t) = returnType t
    returnType t            = t

    generateImports : String
    generateImports
      = List.join "\n" $ map ("import " ++) [ "options"
                                            , "strtabs"
                                            , "tables"
                                            ]

    generateTypes : AppConfig -> Fsm -> String
    generateTypes conf fsm
      = let pre = camelize fsm.name
            env = rootEnv fsm
            rks = liftRecords fsm.model
            oas = liftOutputActions fsm.states fsm.transitions
            ges = nub $ filter applicationExpressionFilter $ flatten $ map expressionsOfTestExpression $ flatten $ map guardsOfTransition $ List1.forget fsm.transitions
            ads = generateActionDelegates indentDelta pre env fsm.states fsm.transitions
            ods = generateOutputDelegates indentDelta pre env oas
            pcds = if conf.ignoreStateAction
                      then ""
                      else generatePortCallbackDelegates indentDelta pre fsm.ports
            gds = generateGuardDelegates indentDelta pre env ges in
            List.join "\n" $ List.filter nonblank [ "type"
                                                  , generateRecords indentDelta rks
                                                  , generateModel indentDelta pre (filter (\(n, _, _) => n /= "state") fsm.model)
                                                  , generateStates indentDelta pre fsm.states
                                                  , ads
                                                  , ods
                                                  , gds
                                                  , pcds
                                                  , generateStateMachine indentDelta pre (0 /= length ads) (0 /= length ods) (0 /= length gds) (0 /= length pcds)
                                                  , generateTransitionActionType indentDelta pre conf.ignoreStateAction fsm.events fsm.ports
                                                  , if conf.ignoreStateAction
                                                       then ""
                                                       else generateStateActionType indentDelta pre
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
                           , List1.join "\n" $ map (generateAttribute (idt + indentDelta)) (("state", (TPrimType PTInt), Nothing) ::: as)
                           ]

        generateStates : Nat -> String -> List1 State -> String
        generateStates idt pre ss
          = List.join "\n" [ (indent idt) ++ pre ++ "State* = enum"
                           , List1.join ",\n" $ map (\(i, x) => generateState (idt + indentDelta) i x) (enumerate ss)
                           ]
          where
            generateState : Nat -> Nat -> State -> String
            generateState idt idx (MkState n _ _ _)
              = (indent idt) ++ ((toNimName . camelize) n) ++ " = " ++ (show idx)

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
              = (indent idt) ++ (toNimFuncName n) ++ "*: " ++ (toNimType t) ++ " {.gcsafe.}"

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
              = let actions = flatten $ map liftActionsFromState $ List1.forget states
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
            generateOutputDelegate idt n t = (indent idt) ++ (toNimName n) ++ "*: " ++ (toNimType t) ++ " {.gcsafe.}"

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
            generateGuardDelegate idt n t = (indent idt) ++ (toNimName n) ++ "*: " ++ (toNimType t) ++ " {.gcsafe.}"

            inferTypeOfExpressions : SortedMap Expression Tipe -> Tipe -> Expression -> Maybe (Name, Tipe)
            inferTypeOfExpressions env firstArgType r@(ApplicationExpression n _) = case fixTypeOfApplicationExpression env (inferType env r) (Just (TPrimType PTBool)) of
                                                                                         Just (TArrow TUnit (TPrimType PTBool)) => Just (n, (TArrow firstArgType (TPrimType PTBool)))
                                                                                         Just a => Just (n, (TArrow firstArgType a))
                                                                                         Nothing => Nothing
            inferTypeOfExpressions _   _            _                             = Nothing

        generatePortCallbackDelegates : Nat -> String -> List Port -> String
        generatePortCallbackDelegates idt pre ports
          = let head = (indent idt) ++ pre ++ "PortCallback* = ref object of RootObj"
                ps = map (generatePortCallbackDelegate (idt + indentDelta)) $ filter portReturnTypeFilter ports
                body = List.join "\n" ps in
                if length ps > Z
                   then List.join "\n" [ head, body ]
                   else ""
          where
            portReturnTypeFilter : Port -> Bool
            portReturnTypeFilter (MkPort pname t)
              = let t' = returnType t in
                    t' /= TUnit

            generatePortCallbackDelegate : Nat -> Port -> String
            generatePortCallbackDelegate idt (MkPort pname t)
              = let t' = returnType t in
                    if t' == TUnit
                       then (indent idt) ++ (toNimName pname) ++ "*: proc (): void {.gcsafe.}"
                       else (indent idt) ++ (toNimName pname) ++ "*: proc (a0: " ++ (toNimType t') ++ "): void {.gcsafe.}"


        generateStateMachine : Nat -> String -> Bool -> Bool -> Bool -> Bool -> String
        generateStateMachine idt pre ads ods gds pcds
          = let head = (indent idt) ++ pre ++ "StateMachine* = ref object of RootObj"
                ad = if ads then (indent (idt + indentDelta)) ++ "action_delegate*: " ++ pre ++ "ActionDelegate" else ""
                od = if ods then (indent (idt + indentDelta)) ++ "output_delegate*: " ++ pre ++ "OutputDelegate" else ""
                gd = if gds then (indent (idt + indentDelta)) ++ "guard_delegate*: " ++ pre ++ "GuardDelegate" else ""
                pcd = if pcds then (indent (idt + indentDelta)) ++ "port_callback_delegate*: " ++ pre ++ "PortCallbackDelegate" else ""
                body = join "\n" $ List.filter nonblank [ad, od, gd, pcd] in
                List.join "\n" [head, body]

        generateTransitionActionType : Nat -> String -> Bool -> List1 Event -> List Port -> String
        generateTransitionActionType idt pre ignoreStateAction es ps
          = let params = parametersOfEvents es
                paramcodes = foldl (\acc, (n, t, _) => acc ++ ", " ++ (toNimName n) ++ "_opt: Option[" ++ (toNimType t) ++ "]" ) ("fsm: " ++ pre ++ "StateMachine, model: " ++ pre ++ "Model, srcstate: int, dststate: int") params
                ports = map (\x => "Option[" ++ (toNimType x) ++ "]") $ filter (\t => t /= TUnit) $ map (\(MkPort _ t) => returnType t) ps
                returns = if ignoreStateAction && (length ports) > 0
                             then "(" ++ List.join ", " ((pre ++ "Model") :: ports) ++ ")"
                             else pre ++ "Model"
                in
                if ignoreStateAction
                   then (indent idt) ++ "TransitionActionFunc = proc (" ++ paramcodes ++ "): " ++ returns ++ " {.gcsafe.}"
                   else (indent idt) ++ "TransitionActionFunc = proc (" ++ paramcodes ++ "): " ++ returns ++ " {.gcsafe.}"

        generateStateActionType : Nat -> String -> String
        generateStateActionType idt pre = (indent idt) ++ "StateActionFunc = proc (fsm: " ++ pre ++ "StateMachine, model: " ++ pre ++ "Model, state: int): " ++ pre ++ "Model {.gcsafe.}"

    generateMatrixs : AppConfig -> Fsm -> String
    generateMatrixs conf fsm
      = let ss   = fsm.states
            ts   = fsm.transitions
            egts = eventGuardTags ts
            ents = map show $ nub $ actionsOfStates (.onEnter) ss
            exts = map show $ nub $ actionsOfStates (.onExit) ss
            ats  = actionTags ts in
            join "\n\n" $ List.filter nonblank [ generateTransitionStateMatrix ss egts ts
                                               , generateTransitionActionMatrix ss egts ts ats
                                               , if conf.ignoreStateAction
                                                    then ""
                                                    else generateStateOnEnterMatrix ss ents
                                               , if conf.ignoreStateAction
                                                    then ""
                                                    else generateStateOnExitMatrix ss exts
                                               ]
      where

        generateTransitionStateMatrix : List1 State -> List String -> List1 Transition -> String
        generateTransitionStateMatrix ss egts ts
          = let matrix = stateMatrix ss egts ts
                code = intMatrixToNim show matrix in
                "const transition_states: array[0.." ++ (show (cast ((length ss) * (length egts)) - 1)) ++ ", int] = [\n" ++ code ++ "\n]"

        generateTransitionActionMatrix : List1 State -> List String -> List1 Transition -> List String -> String
        generateTransitionActionMatrix ss egts ts ats
          = let matrix = transitionActionMatrix ss egts ts ats
                code = intMatrixToNim (\x => "TransitionActionFunc(transition_action" ++ (show x) ++ ")") matrix in
                "const transition_actions: array[0.." ++ (show (cast ((length ss) * (length egts)) - 1)) ++ ", TransitionActionFunc] = [\n" ++ code ++ "\n]"

        generateStateOnEnterMatrix : List1 State -> List String -> String
        generateStateOnEnterMatrix ss tags
          = let matrix = stateActionMatrix (\s, d => d.onEnter) ss tags
                code = intMatrixToNim (\x => "StateActionFunc(on_enter_action" ++ (show x) ++ ")") matrix in
                "const on_enter_actions: array[0.." ++ (show (cast ((length ss) * (length ss)) - 1)) ++ ", StateActionFunc] = [\n" ++ code ++ "\n]"

        generateStateOnExitMatrix : List1 State -> List String -> String
        generateStateOnExitMatrix ss tags
          = let matrix = stateActionMatrix (\s, d => s.onExit) ss tags
                code = intMatrixToNim (\x => "StateActionFunc(on_exit_action" ++ (show x) ++ ")") matrix in
                "const on_exit_actions: array[0.." ++ (show (cast ((length ss) * (length ss)) - 1)) ++ ", StateActionFunc] = [\n" ++ code ++ "\n]"

    generateAction : String -> String -> Bool -> String -> List Port -> (Nat, List Action) -> String
    generateAction pre funpre ignoreStateAction paramcodes ports (idx, acts)
      = let portsigns = map (\(MkPort _ t) => "Option[" ++ (toNimType (returnType t)) ++ "]") ports
            signature = if ignoreStateAction && (length portsigns) > 0
                           then "proc " ++ funpre ++ "_action" ++ (show idx) ++ "(" ++ paramcodes ++ "): (" ++ (List.join ", " ((pre ++ "Model") :: portsigns)) ++ ") {.gcsafe.} ="
                           else "proc " ++ funpre ++ "_action" ++ (show idx) ++ "(" ++ paramcodes ++ "): " ++ pre ++ "Model {.gcsafe.} ="
            usedArgs = liftUsedArgumentsFromActions acts
            (actionsCode, usedPorts) = generateActionsCode ignoreStateAction acts
            ports' = map (\p@(MkPort n t) =>
                       if elemBy (==) p usedPorts
                          then "some(" ++ toNimName ("value-of-port-" ++ n) ++ ")"
                          else "none(" ++ (toNimType (returnType t)) ++ ")") ports
            noneports = map (\(MkPort _ t) => "none(" ++ (toNimType (returnType t)) ++ ")") ports
            body = generateActionsBody indentDelta pre ignoreStateAction actionsCode usedArgs ports' noneports in
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

        generateActionsBody : Nat -> String -> Bool -> List String -> List Name -> List String -> List String -> String
        generateActionsBody idt pre ignoreStateAction bodies ns ports noneports
          = generateActionsBody' idt pre ignoreStateAction bodies ns ports noneports "" "" []
          where
            generateActionsBody' : Nat -> String -> Bool -> List String -> List Name -> List String -> List String -> String -> String -> List String -> String
            generateActionsBody' idt pre ignoreStateAction bodies []        ports noneports acc1 acc2 args
              = if ignoreStateAction && (length ports) > 0
                   then acc1 ++ (join "\n" (map (\x => (indent idt) ++ x) (args ++ bodies ++ ["result = (" ++ (List.join ", " $ "model" :: ports)++ ")\n"]))) ++ acc2
                   else acc1 ++ (join "\n" (map (\x => (indent idt) ++ x) (args ++ bodies ++ ["result = model\n"]))) ++ acc2
            generateActionsBody' idt pre ignoreStateAction bodies (n :: ns) ports noneports acc1 acc2 args
              = if ignoreStateAction && (length ports) > 0
                   then generateActionsBody' (idt + indentDelta) pre ignoreStateAction bodies ns ports noneports (acc1 ++ (indent idt) ++ "if " ++ (toNimName n) ++ "_opt.isSome:\n") ((indent idt) ++ "else:\n" ++ (indent (idt + indentDelta)) ++ "result = (" ++ (List.join ", " ("model" :: noneports)) ++ ")\n" ++ acc2) (("let " ++ (toNimName n) ++ " = " ++ (toNimName n) ++ "_opt.get") :: args)
                   else generateActionsBody' (idt + indentDelta) pre ignoreStateAction bodies ns ports noneports (acc1 ++ (indent idt) ++ "if " ++ (toNimName n) ++ "_opt.isSome:\n") ((indent idt) ++ "else:\n" ++ (indent (idt + indentDelta)) ++ "result = model\n" ++ acc2) (("let " ++ (toNimName n) ++ " = " ++ (toNimName n) ++ "_opt.get") :: args)

        generateActionsCode : Bool -> List Action -> (List String, List Port)
        generateActionsCode
          = generateActionsCode' [] []
          where
            generateActionsCode' : List String -> List Port -> Bool -> List Action -> (List String, List Port)
            generateActionsCode' acc1 acc2 _                 []                             = (reverse acc1, reverse acc2)
            generateActionsCode' acc1 acc2 ignoreStateAction ((AssignmentAction l r) :: xs) = generateActionsCode' (((toNimModelAttribute (show l)) ++ " = " ++ (toNimExpression "fsm.action_delegate" r)) :: acc1) acc2 ignoreStateAction xs
            generateActionsCode' acc1 acc2 True              ((OutputAction p es) :: xs)    = if returnType p.tipe == TUnit
                                                                                                 then generateActionsCode' (("fsm.output_delegate." ++ toNimName(p.name) ++ "(" ++ (List.join ", " (map (toNimExpression "fsm.action_delegate") ((IdentifyExpression "model") :: es))) ++ ")") :: acc1) (p :: acc2) True xs
                                                                                                 else generateActionsCode' (("let " ++ (toNimName ("value-of-port-" ++ p.name)) ++ " = fsm.output_delegate." ++ toNimName(p.name) ++ "(" ++ (List.join ", " (map (toNimExpression "fsm.action_delegate") ((IdentifyExpression "model") :: es))) ++ ")") :: acc1) (p :: acc2) True xs
            generateActionsCode' acc1 acc2 False             ((OutputAction p es) :: xs)    = if returnType p.tipe == TUnit
                                                                                                 then generateActionsCode' (("fsm.output_delegate." ++ toNimName(p.name) ++ "(" ++ (List.join ", " (map (toNimExpression "fsm.action_delegate") ((IdentifyExpression "model") :: es))) ++ ")") :: acc1) (p :: acc2) False xs
                                                                                                 else generateActionsCode' (("fsm.port_callback_delegate." ++ toNimName(p.name) ++ "(fsm.output_delegate." ++ toNimName(p.name) ++ "(" ++ (List.join ", " (map (toNimExpression "fsm.action_delegate") ((IdentifyExpression "model") :: es))) ++ "))") :: acc1) (p :: acc2) False xs
            generateActionsCode' acc1 acc2 ignoreStateAction (_ :: xs)                      = generateActionsCode' acc1 acc2 ignoreStateAction xs

    generateTransitionActions : String -> Bool -> List1 State -> List1 Event -> List1 Transition -> List Port -> String
    generateTransitionActions pre ignoreStateAction ss es ts ps
      = let as = nub $ actionsOfTransitions ts
            params = parametersOfEvents es
            paramcodes = foldl (\acc, (n, t, _) => acc ++ ", " ++ (toNimName n) ++ "_opt: Option[" ++ (toNimType t) ++ "]" ) ("fsm: " ++ pre ++ "StateMachine, model: " ++ pre ++ "Model, srcstate: int, dststate: int") params
            ports = filter (\(MkPort _ t) => (returnType t) /= TUnit) ps
            funcs = map (generateAction pre "transition" ignoreStateAction paramcodes ports) (Data.List.enumerate ([] :: as)) in
            join "\n" funcs

    generateStateActions : (State -> Maybe (List Action)) -> String -> String -> List1 State -> String
    generateStateActions f pre funpre ss
      = let as = nub $ actionsOfStates f ss
            funcs = map (generateAction pre funpre False ("fsm: " ++ pre ++ "StateMachine, model: " ++ pre ++ "Model, state: int") []) (Data.List.enumerate ([] :: as)) in
            join "\n" funcs

    generateActions : AppConfig -> Fsm -> String
    generateActions conf fsm
      = let pre = camelize fsm.name
            ss  = fsm.states
            es  = fsm.events
            ts  = fsm.transitions in
            join "\n" $ List.filter nonblank [ generateTransitionActions pre conf.ignoreStateAction ss es ts fsm.ports
                                             , if conf.ignoreStateAction
                                                  then ""
                                                  else generateStateActions (.onEnter) pre "on_enter" ss
                                             , if conf.ignoreStateAction
                                                  then ""
                                                  else generateStateActions (.onExit) pre "on_exit" ss
                                             ]

    generateEvents : AppConfig -> Fsm -> String
    generateEvents conf fsm
      = let pre = camelize fsm.name
            es = fsm.events
            ts = flatten $ List1.forget $ map (List1.forget . (.triggers)) fsm.transitions
            egts = eventGuardTags fsm.transitions
            params = parametersOfEvents es
            filteredPorts = filter (\(MkPort _ t) => (returnType t) /= TUnit) fsm.ports in
            join "\n\n" $ map (\(e, gs) => generateEvent pre conf.ignoreStateAction filteredPorts e gs egts params) $ eventWithGuards ts
      where
        generateEventBody : Nat -> List String -> Event -> List TestExpression -> String
        generateEventBody idt egts e [] = (indent idt) ++ "let idx = (model.state * " ++ (show (length egts)) ++ ") + " ++ (foldr (\x, acc => show x) "0" (index (show e) egts))
        generateEventBody idt egts e gs = (indent idt) ++ "var idx = 0\n" ++ (((join "\n") . reverse) $ generateEventBody' idt egts e (reverse (sortBy compareTestExpression gs)) True [])
          where
            generateEventBody' : Nat -> List String -> Event -> List TestExpression -> Bool -> List String -> List String
            generateEventBody' idt egts e []        _       acc = ((indent idt) ++ "else:\n" ++ (indent (idt + indentDelta)) ++ "idx = (model.state * " ++ (show (length egts)) ++ ") + " ++ (foldr (\x, acc => show x) "0" (index (show e) egts))) :: acc
            generateEventBody' idt egts e (x :: xs) isFirst acc = let ifcode = if isFirst then "if " else "elif "
                                                                      code = (indent idt) ++ ifcode ++ (toNimTestExpression "fsm.guard_delegate" x) ++ ":\n" ++ (indent (idt + indentDelta)) ++ "idx = (model.state * " ++ (show (length egts)) ++ ") + " ++ (foldr (\x, acc => show x) "0" (index ((show e) ++ (show x)) egts)) in
                                                                      generateEventBody' idt egts e xs False $ code :: acc

        generateEvent : String -> Bool -> List Port -> Event -> List TestExpression -> List String -> List Parameter -> String
        generateEvent pre ignoreStateAction ports e gs egts ps
          = let eparams = e.params
                paramcodes = List.join ", " $ map (\(n, t, _) => (toNimName n) ++ ": " ++ (toNimType t)) (("fsm", TRecord (pre ++ "StateMachine") [], Nothing) :: ("model", TRecord (pre ++ "Model") [], Nothing) :: eparams)
                args = generateArguments eparams ps []
                returnSigns = map (\(MkPort _ t) => "Option[" ++ (toNimType (returnType t)) ++ "]") ports
                signature = if ignoreStateAction && (length returnSigns) > 0
                               then "proc " ++ (toNimName e.name) ++ "*" ++ "(" ++ paramcodes ++ "): (" ++ List.join ", " ((pre ++ "Model") :: returnSigns) ++ ") {.gcsafe.} ="
                               else "proc " ++ (toNimName e.name) ++ "*" ++ "(" ++ paramcodes ++ "): " ++ pre ++ "Model {.gcsafe.} ="
                body = List.join "\n" [ generateEventBody indentDelta egts e gs
                                      , (indent indentDelta) ++ (foldl (\acc, x => acc ++ ", " ++ x) "result = exec(fsm, model, idx" args) ++ ")"
                                      ] in
                signature ++ "\n" ++ body
          where
            generateArguments : List Parameter -> List Parameter -> List String -> List String
            generateArguments eps []                  acc = reverse acc
            generateArguments eps (a@(n, t, _) :: xs) acc = if elemBy (==) a eps
                                                               then generateArguments eps xs $ ("some(" ++ (toNimName n) ++ ")") :: acc
                                                               else generateArguments eps xs $ ("none(" ++ (toNimType t) ++ ")") :: acc

    generateInternalExec : AppConfig -> Fsm -> String
    generateInternalExec conf fsm
      = let pre = camelize fsm.name
            statelen = length fsm.states
            es = fsm.events
            params = parametersOfEvents es
            paramcodes = foldl (\acc, (n, t, _) => acc ++ ", " ++ (toNimName n) ++ "_opt: Option[" ++ (toNimType t) ++ "]") ("fsm: " ++ pre ++ "StateMachine, model: " ++ pre ++ "Model, idx: int") params
            argcodes = List.join ", " ("fsm" :: (if conf.ignoreStateAction then "model" else "model1") :: "srcstate" :: "dststate" :: (map (\(n, _, _) => n ++ "_opt") params))
            filteredPorts = filter (\(MkPort _ t) => (returnType t) /= TUnit) fsm.ports
            returnSigns = map (\(MkPort _ t) => "Option[" ++ (toNimType (returnType t)) ++ "]") filteredPorts
            returnArgs = map (\(MkPort n _) => toNimName ("value-of-port-" ++ n)) filteredPorts in
            List.join "\n" [ if conf.ignoreStateAction && (length returnSigns) > 0
                                then "proc exec(" ++ paramcodes ++ "): (" ++ (List.join ", " ((pre ++ "Model") :: returnSigns)) ++ ") {.gcsafe.} ="
                                else "proc exec(" ++ paramcodes ++ "): " ++ pre ++ "Model {.gcsafe.} ="
                           , (indent indentDelta) ++ "let"
                           , (indent (indentDelta * 2)) ++ "srcstate = model.state"
                           , (indent (indentDelta * 2)) ++ "dststate = transition_states[idx]"
                           , if conf.ignoreStateAction
                                then List.join "\n" [ (indent (indentDelta * 2)) ++ "(" ++ (List.join ", " ("model1" :: returnArgs)) ++  ") = transition_actions[idx](" ++ argcodes ++ ")"
                                                    , (indent indentDelta) ++ "model1.state = dststate"
                                                    , (indent indentDelta) ++ "result = (" ++ (List.join ", " ("model1" :: returnArgs)) ++ ")"
                                                    ]
                                else List.join "\n" [ (indent (indentDelta * 2)) ++ "model1 = on_exit_actions[srcstate * " ++ (show statelen) ++ " + dststate](fsm, model, srcstate)"
                                                    , (indent (indentDelta * 2)) ++ "model2 = transition_actions[idx](" ++ argcodes ++ ")"
                                                    , (indent (indentDelta * 2)) ++ "model3 = on_enter_actions[srcstate * " ++ (show statelen) ++ " + dststate](fsm, model2, dststate)"
                                                    , (indent indentDelta) ++ "model3.state = dststate"
                                                    , (indent indentDelta) ++ "result = model3"
                                                    ]
                           ]

    generateInitModel : Fsm -> String
    generateInitModel fsm
      = let pre = camelize fsm.name
            defaultStateStr = "ord(" ++ pre ++ "State." ++ (camelize fsm.states.head.name) ++ ")"
            startStateStr = fromMaybe defaultStateStr (map (\x => "ord(" ++ pre ++ "State." ++ (camelize x.name) ++ ")") (startState fsm)) in
            List.join "\n" [ "proc init" ++ pre ++ "Model*(): " ++ pre ++ "Model ="
                           , (indent indentDelta) ++ "result = " ++ pre ++ "Model(state: " ++ startStateStr ++ ")"
                           ]

doWork : AppConfig -> IO ()
doWork conf
  = do Right fsm <- loadFsmFromFile conf.src
       | Left err => putStrLn err
       putStrLn $ toNim conf fsm

parseArgs : List String -> Maybe AppConfig
parseArgs
  = parseArgs' Nothing False
  where
    parseArgs' : Maybe String -> Bool -> List String -> Maybe AppConfig
    parseArgs' Nothing    _                 []                              = Nothing
    parseArgs' (Just src) ignoreStateAction []                              = Just (MkAppConfig src ignoreStateAction)
    parseArgs' src        _                 ("--ignore-state-action" :: xs) = parseArgs' src True xs
    parseArgs' _          ignoreStateAction (x :: xs)                       = parseArgs' (Just x) ignoreStateAction xs

usage : String
usage
  = List.join "\n" [ "Usage: pfsm-to-nim [options] <src>"
                   , ""
                   , "Options:"
                   , "  --ignore-state-action    Do not generate actions of states.[default: false]."
                   ]

main : IO ()
main
  = do args <- getArgs
       case tail' args of
            Nothing => putStrLn usage
            Just args' => case parseArgs args' of
                               Just conf => doWork conf
                               Nothing => putStrLn usage
