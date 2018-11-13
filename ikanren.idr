data LVar = MkLVar Int

Eq LVar where
  (MkLVar x) == (MkLVar y) = x == y

Show LVar where
  show (MkLVar x) = "LVar_" ++ show x

data Term a = LVarTerm LVar | Data a | (::) (Term a) (Term a) | Nil

Eq a => Eq (Term a) where
  (LVarTerm x) == (LVarTerm y) = x == y
  (Data x)     == (Data y)     = x == y
  (x :: xs)    == (y :: ys)    = (x == y) && (xs == ys)
  Nil          == Nil          = True
  _            == _            = False

Show a => Show (Term a) where
  show (LVarTerm lv) = show lv
  show (Data x) = show x
  show (x :: xs) = (show x) ++ "::" ++ (show xs)
  show Nil = "Nil"

SMap : Type -> Type
SMap a = List (LVar, Term a)

total lookup : SMap a -> LVar -> Maybe (Term a)
lookup [] var = Nothing
lookup ((entry_k, entry_v) :: smap) var =
  if entry_k == var
    then Just entry_v
    else lookup smap var

total addSubstitution: SMap a -> LVar -> Term a -> SMap a
addSubstitution s v t = (v, t) :: s

-- LookupTheorem1 : (v: LVar) -> (t: Term) -> (s: SMap) -> lookup (addSubstitution s v t) v = Just t
-- LookupTheorem1 v t s = ?P1_rhs1


walk : SMap a -> Term a -> Term a
walk s (LVarTerm v) = case (lookup s v) of
                        Just t => walk s t
                        Nothing => LVarTerm v
walk s x = x

unify : Eq a => Term a -> Term a -> SMap a -> Maybe (SMap a)
unify t u smap =
  let t = walk smap t
      u = walk smap u in

    -- Terms that walk to equal values always unify, but add nothing
    -- to the substitution map
    if t == u
      then Just smap
      else case (t, u) of
        (LVarTerm lv, _) => Just (addSubstitution smap lv u)
        (_, LVarTerm lv) => Just (addSubstitution smap lv t)
        ((x :: xs), (y :: ys)) => (unify x y smap) >>= (unify xs ys)
        (Nil, Nil) => Just smap
        (Data x, Data y) => if x == y
                             then Just smap
                             else Nothing
        (_, _)  => Nothing

-- UnifyTransitive : (s : SMap) -> (t: Term) -> (u : Term) -> unify s t u = unify s u t

-- Lazy streams
data LazyStream a = EmptyStream | MatureStream a (LazyStream a) | ImmatureStream (Inf (LazyStream a))

Semigroup (LazyStream a) where
  EmptyStream              <+> y = y
  (MatureStream head next) <+> y = MatureStream head (next <+> y)
  (ImmatureStream x)       <+> y = ImmatureStream (y <+> x)

Monoid (LazyStream a) where
  neutral = EmptyStream

Functor LazyStream where
  map func EmptyStream              = EmptyStream
  map func (MatureStream head next) = MatureStream (func head) (map func next)
  map func (ImmatureStream x)       = ImmatureStream (map func x)

Applicative LazyStream where
  pure a = MatureStream a EmptyStream

  _                         <*> EmptyStream          = EmptyStream
  EmptyStream               <*> y                    = EmptyStream
  (MatureStream func funcs) <*>  (MatureStream y ys) = MatureStream (func y) (funcs <*> ys)
  (ImmatureStream funcs)    <*> ys                   = ImmatureStream (funcs <*> ys)
  funcs                     <*> (ImmatureStream ys)  = ImmatureStream (funcs <*> ys)

Monad LazyStream where
  EmptyStream              >>= _    = EmptyStream
  (MatureStream head next) >>= func = (func head) <+> (next >>= func)
  (ImmatureStream x)       >>= func = ImmatureStream (x >>= func)

realizeStreamHead : LazyStream a -> LazyStream a
realizeStreamHead (ImmatureStream s) = realizeStreamHead s
realizeStreamHead s = s

take : Nat -> LazyStream a -> List a
take Z _ = []
take (S n) s = case realizeStreamHead s of
                  MatureStream x xs => x :: take n xs
                  _ => []

realizeAll : LazyStream a -> List a
realizeAll EmptyStream = []
realizeAll (MatureStream x xs) = x :: realizeAll xs
realizeAll (ImmatureStream s) = realizeAll s

-- fours : LazyStream Nat
-- fours = MatureStream 4 (ImmatureStream fours)

-- fives : LazyStream Nat
-- fives = MatureStream 5 (ImmatureStream fives)

-- diverge : LazyStream Nat
-- diverge = ImmatureStream diverge

-- take 4 (fours <+> fives) = [4, 5, 4, 5]
-- take 4 (fours <+> diverge) = take 4 (diverge <+> fours) = [4, 4, 4, 4]


-- Interpreter State
record State a where
  constructor MkState
  smap : SMap a
  nextId : Int

emptyState : State a
emptyState = MkState [] 0

-- Goal functions
Goal : Type -> Type
Goal a = State a -> LazyStream (State a)

succeed : Goal a
succeed = pure

fail : Goal a
fail _ = neutral

infixr 10 ===
(===) : Eq a => Term a -> Term a -> Goal a
(===) u v state =
  case unify u v (smap state) of
    Just smap' => pure ( record { smap = smap' } state )
    Nothing => neutral

callFresh : (LVar -> Goal a) -> Goal a
callFresh f state =
  let goal = f (MkLVar (nextId state))
      state' = record { nextId $= (+ 1) } state in
    goal state'

delay : Goal a -> Goal a
delay g state = ImmatureStream (g state)

disj : Goal a -> Goal a -> Goal a
disj g1 g2 state = ((delay g1) state) <+> ((delay g2) state)

conj : Goal a -> Goal a -> Goal a
conj g1 g2 state = (g1 state) >>= g2


-- Sugar

implicit lvarTerm : LVar -> Term a
lvarTerm lv = LVarTerm lv

implicit dataTerm : Eq a => a -> Term a
dataTerm s = Data s

term syntax fresh {x} "in" [body] = callFresh (\x => body)

conjList : List (Goal a) -> Goal a
conjList = foldr conj succeed

conde : List (List (Goal a)) -> Goal a
conde conjClauses = foldr disj fail
                      (map (foldr conj succeed)
                           conjClauses)

(&&) : Goal a -> Goal a -> Goal a
g1 && g2 = conj g1 g2

(||) : Goal a -> Goal a -> Goal a
g1 || g2 = disj g1 g2


run : Nat -> Goal a -> List (SMap a)
run n g = map smap (take n (g emptyState))

runComplete : Goal a -> List (SMap a)
runComplete g = map smap (realizeAll (g emptyState))

-- List relations
conso : Eq a => Term a -> Term a -> Term a -> Goal a
conso a d l = (a :: d) === l

firsto : Eq a => Term a -> Term a -> Goal a
firsto a l = fresh d in (a :: d) === l

resto : Eq a => Term a -> Term a -> Goal a
resto d l = fresh a in (a :: d) === l

nilo : Eq a => Term a -> Goal a
nilo l = l === Nil

appendo : Eq a => Term a -> Term a -> Term a -> Goal a
appendo front back l =
  fresh a in
  fresh d in
  fresh rec in
    disj
      (nilo front && back === l)
      ((a :: d) === front &&
       appendo d back rec &&
       (a :: rec) === l)


-- foobar : Goal String
-- foobar =
--   fresh a in
--     disj (a === "foo")
--          (a === "bar")

-- foos : Term -> Goal String
-- foos a =
--   disj (a === "foo")
--        (foos a)

-- bars : Term -> Goal String
-- bars a =
--   disj (a === "bar")
--        (bars a)

-- foobars : Term -> Goal String
-- foobars a = disj (foos a) (bars a)

-- condeTest : Goal String
-- condeTest =
--   fresh a in
--   fresh b in
--     conde [[a === "One",   b === "Two"],
--            [a === "Alpha", b === "Beta"]]

-- main: IO ()
-- main = putStrLn(show (runComplete condeTest))
