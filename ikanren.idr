data LVar = MkLVar Int

Eq LVar where
  (MkLVar x) == (MkLVar y) = x == y

Show LVar where
  show (MkLVar x) = "LVar_" ++ show x

implicit lvarTerm : LVar -> Term
lvarTerm lv = LVarTerm lv
data Term = LVarTerm LVar | Data String

implicit dataTerm : String -> Term
dataTerm s = Data s
Eq Term where
  (LVarTerm x) == (LVarTerm y) = x == y
  (Data x)     == (Data y)     = x == y
  _            == _            = False

Show Term where
  show (LVarTerm lv) = show lv
  show (Data x) = show x

SMap : Type
SMap = List (LVar, Term)

total lookup : SMap -> LVar -> Maybe Term
lookup [] var = Nothing
lookup ((entry_k, entry_v) :: smap) var =
  if entry_k == var
    then Just entry_v
    else lookup smap var

total addSubstitution: SMap -> LVar -> Term -> SMap
addSubstitution s v t = (v, t) :: s

-- LookupTheorem1 : (v: LVar) -> (t: Term) -> (s: SMap) -> lookup (addSubstitution s v t) v = Just t
-- LookupTheorem1 v t s = ?P1_rhs1


walk : SMap -> Term -> Term
walk s (LVarTerm v) = case (lookup s v) of
                        Just t => walk s t
                        Nothing => LVarTerm v
walk s x = x

unify : SMap -> Term -> Term -> Maybe SMap
unify s t u =
  let t = walk s t
      u = walk s u in

    -- Terms that walk to equal values always unify, but add nothing
    -- to the substitution map
    if t == u
      then Just s
      else case (t, u) of
        (LVarTerm lv, _) => Just (addSubstitution s lv u)
        (_, LVarTerm lv) => Just (addSubstitution s lv t)
        (Data x, Data y) => if x == y
                             then Just s
                             else Nothing

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

-- take 4 (fours <+> fives) = [4, 5, 4, 5]


-- Interpreter State
record State where
  constructor MkState
  smap : SMap
  nextId : Int

emptyState : State
emptyState = MkState [] 0

-- Goal functions
Goal : Type
Goal = State -> LazyStream State

infixr 10 ===
(===) : Term -> Term -> Goal
(===) u v state =
  case unify (smap state) u v  of
    Just smap' => pure ( record { smap = smap' } state )
    Nothing => neutral

callFresh : (LVar -> Goal) -> Goal
callFresh f state =
  let goal = f (MkLVar (nextId state))
      state' = record { nextId $= (+ 1) } state in
    goal state'

delay : Goal -> Goal
delay g state = ImmatureStream (g state)

disj : Goal -> Goal -> Goal
disj g1 g2 state = ((delay g1) state) <+> ((delay g2) state)

conj : Goal -> Goal -> Goal
conj g1 g2 state = (g1 state) >>= g2

-- foobar : Goal
-- foobar = callFresh
--   (\a => disj (a === "foo")
--               (a === "bar"))

