module Pfsm.Nim

import Data.Maybe
import Data.Fin
import Data.List
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
import Pfsm.Parser

indentDelta : Nat
indentDelta = 2

zipEventWithGuards : List Event -> List Trigger -> List (Event, List TestExpression)
zipEventWithGuards es ts
  = zipEventWithGuards' es ts empty
  where
    zipEventWithGuards' : List Event -> List Trigger -> SortedMap Event (List TestExpression) -> List (Event, List TestExpression)
    zipEventWithGuards' es []                                  acc = toList acc
    zipEventWithGuards' es ((MkTrigger _ er (Just g) _) :: ts) acc = case derefEvent er es of
                                                                          Nothing => zipEventWithGuards' es ts acc
                                                                          Just e => case lookup e acc of
                                                                                         Just gs => zipEventWithGuards' es ts $ insert e (nub (g :: gs)) acc
                                                                                         Nothing => zipEventWithGuards' es ts $ insert e [g] acc
    zipEventWithGuards' es ((MkTrigger _ er Nothing _) :: ts)  acc = case derefEvent er es of
                                                                          Nothing => zipEventWithGuards' es ts acc
                                                                          Just e => case lookup e acc of
                                                                                         Just gs => zipEventWithGuards' es ts acc
                                                                                         Nothing => zipEventWithGuards' es ts $ insert e [] acc

eventGuardTags : List Event -> List Transition -> List String
eventGuardTags evts trans
  = let triggers = flatten (map (\x => x.triggers) trans) in
        eventGuardTags' (zipEventWithGuards evts triggers) []
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

stateMatrix : (states: List State) -> List Event -> (eventGuards: List String) -> List Transition -> Matrix (1 + (length states)) (length eventGuards) Int
stateMatrix ss es egts ts
  = let ssstr = map (\x => x.name) ss
        matrix = create (1 + (length ss)) (length egts) (the Int 0) in
        foldl (\acc, x => let s = Data.List.index x.src ssstr
                              d = Data.List.index x.dst ssstr
                              v = Just (-) <*> map cast d <*> map cast s in
                              foldl (\acc', y => updateMatrix es egts s v y acc') acc x.triggers
                              ) matrix ts
  where
    updateMatrix : {row: Nat} -> (events: List Event) -> (eventGuards: List String) -> Maybe Nat -> Maybe Int -> Trigger -> Matrix row (length eventGuards) Int -> Matrix row (length eventGuards) Int
    updateMatrix es egts s v (MkTrigger _ er Nothing _)  m = let e : Maybe Nat
                                                                 e = fromMaybe Nothing $ map (flip Data.List.index egts) (map show (derefEvent er es)) in
                                                                 updateStateMatrix (map (+ 1) s) e v m
    updateMatrix es egts s v (MkTrigger _ er (Just g) _) m = let e : Maybe Nat
                                                                 e = fromMaybe Nothing $ map (flip Data.List.index egts) (map (\x => (show x) ++ show g) (derefEvent er es)) in
                                                                 updateStateMatrix (map (+ 1) s) e v m

actionTags : List Transition -> List String
actionTags trans
  = SortedSet.toList $ foldl (\acc, x => foldl (\acc', y => actionTags' y acc') acc x.triggers) empty trans
  where
    actionTags' : Trigger -> SortedSet String -> SortedSet String
    actionTags' (MkTrigger _ _ _ Nothing)   acc = acc
    actionTags' (MkTrigger _ _ _ (Just [])) acc = acc
    actionTags' (MkTrigger _ _ _ (Just as)) acc = insert (foldl (\acc, x => acc ++ (show x)) "" as) acc

transitionActionMatrix : (states: List State) -> List Event -> (eventGuards: List String) -> List Transition -> List String -> Matrix (1 + length states) (length eventGuards) Int
transitionActionMatrix ss es egts ts ats
  = let ssstr = map (\x => x.name) ss
        matrix = create (1 + (length ss)) (length egts) (the Int 0) in
        foldl (\acc, x => let s = map (+ 1) $ Data.List.index x.src ssstr in
                              foldl (\acc', y => calcAction es egts ats s y acc') acc x.triggers
                              ) matrix ts
  where
    calcAction : {r: Nat} -> List Event -> (eventGuards: List String) -> List String -> Maybe Nat -> Trigger -> Matrix r (length eventGuards) Int -> Matrix r (length eventGuards) Int
    calcAction es egts ats s (MkTrigger _ e _        Nothing)   m = m
    calcAction es egts ats s (MkTrigger _ e _        (Just [])) m = m
    calcAction es egts ats s (MkTrigger _ e Nothing  (Just as)) m = let c = fromMaybe Nothing $ map (\x => Data.List.index (show x) egts) (derefEvent e es)
                                                                        v = map ((+ 1) . cast . natToInteger) $ Data.List.index (foldl (\acc, x => acc ++ (show x)) "" as) ats in
                                                                        updateStateMatrix s c v m
    calcAction es egts ats s (MkTrigger _ e (Just g) (Just as)) m = let c = fromMaybe Nothing $ map (\x => Data.List.index ((show x) ++ (show g)) egts) (derefEvent e es)
                                                                        v = map ((+ 1) . cast . natToInteger) $ Data.List.index (foldl (\acc, x => acc ++ (show x)) "" as) ats in
                                                                        updateStateMatrix s c v m

stateActionMatrix : (State -> State -> Maybe (List Action)) -> (states : List State) -> List String -> Matrix (1 + length states) (1 + length states) Int
stateActionMatrix f ss tags
  = calcActions f ss ss tags $ create (1 + length ss) (1 + length ss) 0
  where
    calcActionVector : {dim : Nat} -> (State -> State -> Maybe (List Action)) -> Nat -> State -> List State -> List State -> List String -> Matrix dim dim Int -> Matrix dim dim Int
    calcActionVector f si s []        ss tags m = m
    calcActionVector f si s (x :: xs) ss tags m = case f s x of
                                                       Just as => if s == x
                                                                     then calcActionVector f si s xs ss tags m
                                                                     else calcActionVector f si s xs ss tags $ updateStateMatrix (Just (si + 1)) (map (+ 1) (Data.List.index x ss)) (map ((+ 1) . cast . natToInteger) (Data.List.index (show as) tags)) m
                                                       Nothing => calcActionVector f si s xs ss tags m

    calcActions : (State -> State -> Maybe (List Action)) -> List State -> (states: List State) -> List String -> Matrix (1 + length states) (1 + length states) Int -> Matrix (1 + length states) (1 + length states) Int
    calcActions f []        _      _    m = m
    calcActions f (x :: xs) states tags m = calcActions f xs states tags $ calcActionVector f (minus (minus (length states) (length xs)) 1) x states states tags m

nimBuiltinTypes : List String
nimBuiltinTypes = [ "int" , "int8" , "int16" , "int32" , "int64" , "uint" , "uint8" , "uint16" , "uint32" , "uint64" , "float" , "floa t32" , "float64" , "true" , "false" , "char" , "string" , "cstring" ]

nimKeywords : List String
nimKeywords = [ "addr" , "and" , "as" , "asm" , "bind" , "block" , "break" , "case" , "cast" , "concept" , "const" , "continue" , "converter" , "defer" , "discard" , "distinct" , "div" , "do" , "elif" , "else" , "end" , "enum" , "except" , "export" , "finally" , "for" , "from" , "func" , "if" , "import" , "in" , "include" , "interface" , "is" , "isnot" , "iterator" , "let" , "macro" , "method" , "mixin" , "mod" , "nil" , "not" , "notin" , "object" , "of" , "or" , "out" , "proc" , "ptr" , "raise" , "ref" , "return" , "shl" , "shr" , "static" , "template" , "try" , "tuple" , "type" , "using" , "var" , "when" , "while" , "xor" , "yield" ]

intMatrixToNim : {r, c: Nat} -> (Int -> String) -> Matrix r c Int -> String
intMatrixToNim {r} {c} f (MkMatrix xs) = Data.Vect.join ",\n" (map (\x => (indent indentDelta) ++ x) (map (\x => Data.Vect.join ", " (map f x)) xs))

primToNimType : PrimType -> String
primToNimType t
  = case t of
         PTBool   => "bool"
         PTByte   => "uint8"
         PTChar   => "char"
         PTShort  => "int16"
         PTUShort => "uint16"
         PTInt    => "int"
         PTUInt   => "uint"
         PTLong   => "int64"
         PTULong  => "uint64"
         PTReal   => "float64"
         PTString => "string"

toNimName : Name -> String
toNimName n
  = let n' = normalize n in
    if elemBy (==) n' nimKeywords
       then "my_" ++ n'
       else n'
  where
    mappings : List (String, String)
    mappings =  [ (" ", "_")
                , ("-", "_")
                , ("+", "plus")
                ]
    normalize : Name -> String
    normalize n = foldl (\acc, x => replaceAll (fst x) (snd x) acc) n mappings

toNimType : Tipe -> String
toNimType TUnit          = "void"
toNimType (TPrimType t)  = primToNimType t
toNimType (TList t)      = "seq[" ++ (toNimType t) ++ "]"
toNimType (TDict k v)    = "table[" ++ (primToNimType k) ++ "," ++ (toNimType v) ++ "]"
toNimType (TRecord n ts) = toNimName n
toNimType t@(TArrow a b) = case liftArrowParams t [] of
                                []      => toNimFuncType []           TUnit
                                x :: xs => toNimFuncType (reverse xs) x
                        where
                          liftArrowParams : Tipe -> List Tipe -> List Tipe
                          liftArrowParams (TArrow a b@(TArrow _ _)) acc = liftArrowParams b (a :: acc)
                          liftArrowParams (TArrow a b)              acc = b :: (a :: acc)
                          liftArrowParams _                         acc = acc

                          toNimFuncType : List Tipe -> Tipe -> String
                          toNimFuncType as r
                              = let args = join ", " (map (\(i, x) => "a" ++ (show i) ++ ": " ++ toNimType(x)) (enumerate as))
                                    ret  = toNimType r in
                                    "proc (" ++ args ++ "): " ++ ret

toNimModelAttribute : String -> String
toNimModelAttribute "@" = "model"
toNimModelAttribute a
  = if isPrefixOf "@" a
       then "model." ++ toNimName (substr 1 (minus (length a) 1) a)
       else toNimName a

toNimExpression : String -> Expression -> String
toNimExpression "fsm.guard_delegate" (ApplicationExpression n es) = "fsm.guard_delegate" ++ "." ++ (toNimName n) ++ "(" ++ (join ", " (map (toNimExpression "fsm.guard_delegate") ((IdentifyExpression "model") :: es))) ++ ")"
toNimExpression caller (ApplicationExpression n es) = caller ++ "." ++ (toNimName n) ++ "(" ++ (join ", " (map (toNimExpression caller) es)) ++ ")"
toNimExpression _      (BooleanExpression True)     = "true"
toNimExpression _      (BooleanExpression False)    = "false"
toNimExpression _      (IdentifyExpression i)       = toNimModelAttribute i
toNimExpression _      (IntegerLiteralExpression i) = show i
toNimExpression _      (RealLiteralExpression r)    = show r
toNimExpression _      (StringLiteralExpression s)  = show s

toNimCompareOperation : CompareOperation -> String
toNimCompareOperation NotEqualsToOperation         = "!="
toNimCompareOperation EqualsToOperation            = "=="
toNimCompareOperation LessThanOperation            = "<"
toNimCompareOperation LessThanOrEqualsToOperation  = "<="
toNimCompareOperation GreatThanOperation           = ">"
toNimCompareOperation GreatThanOrEqualsToOperation = ">="

toNimTestExpression : TestExpression -> String
toNimTestExpression (PrimitiveTestExpression e) = toNimExpression "fsm.guard_delegate" e
toNimTestExpression (BinaryTestExpression op e1 e2) = (toNimTestExpression e1) ++ " " ++ (show op) ++ " " ++ (toNimTestExpression e2)
toNimTestExpression (UnaryTestExpression op e) = (show op) ++ " " ++ (toNimTestExpression e)
toNimTestExpression (CompareExpression op e1 e2) = (toNimExpression "fsm.guard_delegate" e1) ++ " " ++ (toNimCompareOperation op) ++ " " ++ (toNimExpression "fsm.guard_delegate" e2)

%hide Data.Vect.(::)

toNim : Fsm -> String
toNim fsm
  = join "\n\n" [ generateImports
                , generateTypes fsm
                , generateActions fsm
                , generateMatrixs fsm
                , generateInternalExec fsm
                , generateEvents fsm
                , generateInitModel fsm
                ]
  where
    generateImports : String
    generateImports = "import options\n"

    generateTypes : Fsm -> String
    generateTypes fsm
      = let pre = camelize fsm.name
            env = rootEnv fsm
            aas = assignmentActions fsm
            oas = outputActions fsm
            ges = nub $ filter applicationExpressionFilter $ flatten $ map expressionsOfTestExpression $ flatten $ map guardsOfTransition fsm.transitions
            ads = generateActionDelegates indentDelta pre env aas
            ods = generateOutputDelegates indentDelta pre env oas
            gds = generateGuardDelegates indentDelta pre env ges in
            join "\n" [ "type"
                      , generateModel indentDelta pre (filter (\(n, _, _) => n /= "state" ) fsm.model)
                      , generateStates indentDelta pre fsm.states
                      , ads
                      , ods
                      , gds
                      , generateStateMachine indentDelta pre (0 /= length ads) (0 /= length ods) (0 /= length gds)
                      , generateTransitionActionType indentDelta pre fsm.events
                      , generateStateActionType indentDelta pre
                      ]
      where
        generateModel : Nat -> String -> List Parameter -> String
        generateModel idt pre as
          = join "\n" [ (indent idt) ++ pre ++ "Model* = ref object of RootObj"
                      , join "\n" $ map (generateAttribute (idt + indentDelta)) (("state", (TPrimType PTInt), Nothing) :: as)
                      ]
          where
            generateAttribute : Nat -> Parameter -> String
            generateAttribute idt (n, t, _)
              = (indent idt) ++ (toNimName n) ++ "*: " ++ (toNimType t)

        generateStates : Nat -> String -> List State -> String
        generateStates idt pre ss
          = join "\n" [ (indent idt) ++ pre ++ "State* = enum"
                      , join "\n" $ map (\(i, x) => generateState (idt + indentDelta) i x) (enumerate ss)
                      ]
          where
            generateState : Nat -> Nat -> State -> String
            generateState idt idx (MkState n _ _ _)
              = (indent idt) ++ (camelize (toNimName n)) ++ " = " ++ (show (idx + 1))

        liftArrowParams : Tipe -> List Tipe -> List Tipe
        liftArrowParams (TArrow a b@(TArrow _ _)) acc = liftArrowParams b (a :: acc)
        liftArrowParams (TArrow a b)              acc = b :: (a :: acc)
        liftArrowParams _                         acc = acc

        fixTypeOfApplicationExpression : SortedMap Expression Tipe -> Maybe Tipe -> Maybe Tipe -> Maybe Tipe
        fixTypeOfApplicationExpression env (Just ats@(TArrow a b)) (Just rt) = case liftArrowParams ats [] of
                                                                                    []        => Just (TArrow TUnit rt)
                                                                                    (x :: xs) => Just (constructTArrow (reverse xs) rt)
        fixTypeOfApplicationExpression env _                       (Just rt) = Just (TArrow TUnit rt)
        fixTypeOfApplicationExpression env _                       _         = Nothing

        generateActionDelegates : Nat -> String -> SortedMap Expression Tipe -> List Action -> String
        generateActionDelegates idt pre env as
          = let eps = SortedSet.toList $ foldl (\acc, x => applicationExpressionOfAction x acc) SortedSet.empty as
                fps = foldl (\acc, x => case x of Just x' => x' :: acc; Nothing => acc) (the (List (Name, Tipe)) []) $ map (inferTypeOfExpressions env) eps
                head = (indent idt) ++ pre ++ "ActionDelegate* = ref object of RootObj"
                body = join "\n" (map (\(n, t) => (generateActionDelegate (idt + indentDelta) n t)) fps) in
                if length fps > Z
                   then join "\n" [head, body]
                   else ""
          where
            generateActionDelegate: Nat -> Name -> Tipe -> String
            generateActionDelegate idt n t = (indent idt) ++ (toNimName n) ++ "*: " ++ (toNimType t)

            applicationExpressionOfAction : Action -> SortedSet (Expression, Expression) -> SortedSet (Expression, Expression)
            applicationExpressionOfAction (AssignmentAction l e@(ApplicationExpression _ _)) acc = insert (l, e) acc
            applicationExpressionOfAction _                                                  acc = acc

            inferTypeOfExpressions : SortedMap Expression Tipe -> (Expression, Expression) -> Maybe (String, Tipe)
            inferTypeOfExpressions env (l, r@(ApplicationExpression n _)) = Just (n, maybe TUnit id (fixTypeOfApplicationExpression env (inferType env r) (inferType env l)))
            inferTypeOfExpressions _   _                                  = Nothing

        generateOutputDelegates : Nat -> String -> SortedMap Expression Tipe -> List Action -> String
        generateOutputDelegates idt pre env as
          = let
                oes = (SortedMap.toList . (foldl (\acc, x => expressionOfOutputAction x acc) SortedMap.empty)) as
                fps = map (\(n, t) => (n, TArrow (TRecord (pre ++ "Model") []) t)) $ map (inferTypeOfExpressions env) oes
                head = (indent idt) ++ pre ++ "OutputDelegate* = ref object of RootObj"
                body = join "\n" (map (\(n, t) => (generateOutputDelegate (idt + indentDelta) n t)) fps) in
                if length fps > 0
                   then join "\n" [head, body]
                   else ""
          where
            generateOutputDelegate : Nat -> Name -> Tipe -> String
            generateOutputDelegate idt n t = (indent idt) ++ (toNimName n) ++ "*: " ++ (toNimType t)

            expressionOfOutputAction : Action -> SortedMap Name (List Expression) -> SortedMap Name (List Expression)
            expressionOfOutputAction (OutputAction n es) acc = insert n es acc
            expressionOfOutputAction _                   acc = acc

            inferTypeOfExpressions : SortedMap Expression Tipe -> (Name, List Expression) -> (Name, Tipe)
            inferTypeOfExpressions env (n, es) = (n, constructTArrow (reverse (map ((maybe TUnit id ) . (inferType env)) es)) TUnit)

        generateGuardDelegates : Nat -> String -> SortedMap Expression Tipe -> List Expression -> String
        generateGuardDelegates idt pre env ges
          = let fps = foldl (\acc, x => case x of Just x' => x' :: acc; Nothing => acc) (the (List (Name, Tipe)) []) $ map (inferTypeOfExpressions env (TRecord (pre ++ "Model") [])) ges
                head = (indent idt) ++ pre ++ "GuardDelegate* = ref object of RootObj"
                body = join "\n" (map (\(n, t) => (generateGuardDelegate (idt + indentDelta) n t)) fps) in
                if length fps > Z
                   then join "\n" [head, body]
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
                body = join "\n" (filter (\x => 0 /= length x) [ad, od, gd]) in
                join "\n" [head, body]

        generateTransitionActionType : Nat -> String -> List Event -> String
        generateTransitionActionType idt pre es
          = let params = parametersOfEvents es
                paramcodes = foldl (\acc, (n, t, _) => acc ++ ", " ++ (toNimName n) ++ "_opt: Option[" ++ (toNimType t) ++ "]" ) ("fsm: " ++ pre ++ "StateMachine, model: " ++ pre ++ "Model") params in
                (indent idt) ++ "TransitionActionFunc = proc (" ++ paramcodes ++ "): " ++ pre ++ "Model"

        generateStateActionType : Nat -> String -> String
        generateStateActionType idt pre = (indent idt) ++ "StateActionFunc = proc (fsm: " ++ pre ++ "StateMachine, model: " ++ pre ++ "Model): " ++ pre ++ "Model"

    generateMatrixs : Fsm -> String
    generateMatrixs fsm
      = let ss   = fsm.states
            es   = fsm.events
            ts   = fsm.transitions
            egts = eventGuardTags es ts
            ents = map show $ actionsOfStates (.onEnter) ss
            exts = map show $ actionsOfStates (.onExit) ss
            ats  = actionTags ts in
            join "\n\n" [ generateTransitionStateMatrix ss es egts ts
                        , generateTransitionActionMatrix ss es egts ts ats
                        , generateStateOnEnterMatrix ss ents
                        , generateStateOnExitMatrix ss exts
                        ]
      where

        generateTransitionStateMatrix : List State -> List Event -> List String -> List Transition -> String
        generateTransitionStateMatrix ss es egts ts
          = let matrix = stateMatrix ss es egts ts
                code = intMatrixToNim show matrix in
                "const transition_states: array[0.." ++ (show (cast (((length ss) + 1) * (length egts)) - 1)) ++ ", int] = [\n" ++ code ++ "\n]"

        generateTransitionActionMatrix : List State -> List Event -> List String -> List Transition -> List String -> String
        generateTransitionActionMatrix ss es egts ts ats
          = let matrix = transitionActionMatrix ss es egts ts ats
                code = intMatrixToNim (\x => "TransitionActionFunc(transition_action" ++ (show x) ++ ")") matrix in
                "const transition_actions: array[0.." ++ (show (cast (((length ss) + 1) * (length egts)) - 1)) ++ ", TransitionActionFunc] = [\n" ++ code ++ "\n]"

        generateStateOnEnterMatrix : List State -> List String -> String
        generateStateOnEnterMatrix ss tags
          = let matrix = stateActionMatrix (\s, d => d.onEnter) ss tags
                code = intMatrixToNim (\x => "StateActionFunc(on_enter_action" ++ (show x) ++ ")") matrix in
                "const on_enter_actions: array[0.." ++ (show (cast (((length ss) + 1) * ((length ss) + 1)) - 1)) ++ ", StateActionFunc] = [\n" ++ code ++ "\n]"

        generateStateOnExitMatrix : List State -> List String -> String
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
          = liftUsedArgumentsFromActions' acts []
          where
            liftUsedArgumentsFromExpression : Expression -> List Name
            liftUsedArgumentsFromExpression (IdentifyExpression s)       = if isPrefixOf "@" s
                                                                              then []
                                                                              else [s]
            liftUsedArgumentsFromExpression (ApplicationExpression _ ss) = concat $ map liftUsedArgumentsFromExpression ss
            liftUsedArgumentsFromExpression _                            = []

            liftUsedArgumentsFromActions' : List Action -> List Name -> List Name
            liftUsedArgumentsFromActions' []                             acc = acc
            liftUsedArgumentsFromActions' ((AssignmentAction _ e) :: xs) acc = liftUsedArgumentsFromActions' xs (acc ++ liftUsedArgumentsFromExpression e)
            liftUsedArgumentsFromActions' ((OutputAction _ es) :: xs)    acc = liftUsedArgumentsFromActions' xs (foldl (\acc', x => acc' ++ (liftUsedArgumentsFromExpression x)) acc es)
            liftUsedArgumentsFromActions' (_ :: xs)                      acc = liftUsedArgumentsFromActions' xs acc

        generateActionsBody : Nat -> String -> List String -> List Name -> String
        generateActionsBody idt pre bodies ns
          = generateActionsBody' idt pre bodies ns "" "" []
          where
            generateActionsBody' : Nat -> String -> List String -> List Name -> String -> String -> List String -> String
            generateActionsBody' idt pre bodies []        acc1 acc2 args = acc1 ++ (join "\n" (map (\x => (indent idt) ++ x) (args ++ bodies ++ ["result = model\n"]))) ++ acc2
            generateActionsBody' idt pre bodies (n :: ns) acc1 acc2 args = generateActionsBody' (idt + indentDelta) pre bodies ns (acc1 ++ (indent idt) ++ "if " ++ (toNimName n) ++ "_opt.isSome:\n") ((indent idt) ++ "else:\n" ++ (indent (idt + indentDelta)) ++ "result = model\n" ++ acc2) (("let " ++ (toNimName n) ++ " = " ++ (toNimName n) ++ "_opt.get") :: args)

        generateActionsCode : List Action -> List String
        generateActionsCode acts
          = generateActionsCode' acts []
          where
            generateActionsCode' : List Action -> List String -> List String
            generateActionsCode' []                             acc = acc
            generateActionsCode' ((AssignmentAction l r) :: xs) acc = generateActionsCode' xs $ ((toNimModelAttribute (show l)) ++ " = " ++ (toNimExpression "fsm.action_delegate" r)) :: acc
            generateActionsCode' ((OutputAction n es) :: xs)    acc = generateActionsCode' xs $ ("fsm.output_delegate." ++ toNimName(n) ++ "(" ++ (join ", " (map (toNimExpression "fsm.output_delegate") ((IdentifyExpression "model") :: es))) ++ ")") :: acc
            generateActionsCode' (_ :: xs)                      acc = generateActionsCode' xs acc

    generateTransitionActions : String -> List State -> List Event -> List Transition -> String
    generateTransitionActions pre ss es ts
      = let as = actionsOfTransitions ts
            params = parametersOfEvents es
            paramcodes = foldl (\acc, (n, t, _) => acc ++ ", " ++ (toNimName n) ++ "_opt: Option[" ++ (toNimType t) ++ "]" ) ("fsm: " ++ pre ++ "StateMachine, model: " ++ pre ++ "Model") params
            funcs = map (generateAction pre "transition" paramcodes) (Data.List.enumerate ([] :: as)) in
            join "\n\n" funcs

    generateStateActions : (State -> Maybe (List Action)) -> String -> String -> List State -> String
    generateStateActions f pre funpre ss
      = let as = actionsOfStates f ss
            funcs = map (generateAction pre funpre ("fsm: " ++ pre ++ "StateMachine, model: " ++ pre ++ "Model")) (Data.List.enumerate ([] :: as)) in
            join "\n\n" funcs

    generateActions : Fsm -> String
    generateActions fsm
      = let pre = camelize fsm.name
            ss  = fsm.states
            es  = fsm.events
            ts  = fsm.transitions in
            join "\n\n" [ generateTransitionActions pre ss es ts
                        , generateStateActions (.onEnter) pre "on_enter" ss
                        , generateStateActions (.onExit) pre "on_exit" ss
                        ]

    generateEvents : Fsm -> String
    generateEvents fsm
      = let pre    = camelize fsm.name
            es     = fsm.events
            ts     = flatten $ map (.triggers) fsm.transitions
            egts   = eventGuardTags es fsm.transitions
            params = parametersOfEvents es in
            join "\n\n" $ map (\(e, gs) => generateEvent pre e gs egts params) $ zipEventWithGuards es ts
      where
        generateEventBody : Nat -> List String -> Event -> List TestExpression -> String
        generateEventBody idt egts e []           = (indent idt) ++ "let idx = (model.state * " ++ (show (length egts)) ++ ") + " ++ (foldr (\x, acc => show x) "0" (index (show e) egts))
        generateEventBody idt egts e gs@(x :: xs) = (indent idt) ++ "var idx = 0\n" ++ (((join "\n") . reverse) $ generateEventBody' idt egts e gs True [])
          where
            generateEventBody' : Nat -> List String -> Event -> List TestExpression -> Bool -> List String -> List String
            generateEventBody' idt egts e []        _       acc = ((indent idt) ++ "else:\n" ++ (indent (idt + indentDelta)) ++ "idx = (model.state * " ++ (show (length egts)) ++ ") + " ++ (foldr (\x, acc => show x) "0" (index (show e) egts))) :: acc
            generateEventBody' idt egts e (x :: xs) isFirst acc = let ifcode = if isFirst then "if " else "elif "
                                                                      code = (indent idt) ++ ifcode ++ (toNimTestExpression x) ++ ":\n" ++ (indent (idt + indentDelta)) ++ "idx = (model.state * " ++ (show (length egts)) ++ ") + " ++ (foldr (\x, acc => show x) "0" (index ((show e) ++ (show x)) egts)) in
                                                                      generateEventBody' idt egts e xs False $ code :: acc

        generateEvent : String -> Event -> List TestExpression -> List String -> List Parameter -> String
        generateEvent pre e gs egts ps
          = let eparams = e.params
                paramcodes = join ", " $ map (\(n, t, _) => (toNimName n) ++ ": " ++ (toNimType t)) (("fsm", TRecord (pre ++ "StateMachine") [], Nothing) :: (("model", TRecord (pre ++ "Model") [], Nothing) :: eparams))
                args = generateArguments eparams ps []
                signature = "proc " ++ (toNimName e.name) ++ "*" ++ "(" ++ paramcodes ++ "): " ++ pre ++ "Model ="
                body = join "\n" [ generateEventBody indentDelta egts e gs
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
            join "\n" [ "proc exec(" ++ paramcodes ++ "): " ++ pre ++ "Model ="
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
            defaultStateStr = case Data.List.head' fsm.states of
                                   Just s => "ord(" ++ pre ++ "State." ++ (camelize s.name) ++ ")"
                                   Nothing => "0"
            startStateStr = fromMaybe defaultStateStr (map (\x => "ord(" ++ pre ++ "State." ++ (camelize x.name) ++ ")") (startState fsm)) in
            join "\n" [ "proc init" ++ pre ++ "Model*(): " ++ pre ++ "Model ="
                      , (indent indentDelta) ++ "result = " ++ pre ++ "Model(state: " ++ startStateStr ++ ")"
                      ]


loadFsm : String -> Either String Fsm
loadFsm src
  = case parseSExp src of
         Left (Error e _) => Left e
         Right (sexp, _) => case analyse sexp of
                                 Left (Error e _) => Left e
                                 Right (fsm, _) => case check fsm defaultCheckingRules of
                                                        Just errs => Left $ foldl (\a, x => a ++ "\n" ++ x) "" errs
                                                        Nothing => Right fsm

doWork : String -> IO ()
doWork src
  = do
    r <- readFile src
    case r of
         Left e => putStrLn $ show e
         Right c => case loadFsm c of
                         Left e => putStrLn $ e
                         Right fsm => putStrLn $ toNim fsm

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
