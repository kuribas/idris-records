module Records
import Data.String
import Data.Maybe
import Data.List
import Data.List.Elem
import Data.Vect
import Data.Morphisms
import Decidable.Equality
import Data.IOArray.Prims
import Prelude

infixr 10 :->
infixr 10 !!
infixr 3 <*~>
infixr 4 <$~>

public export
RecordSpec : Type -> Type
RecordSpec k = List (String, k)

public export
data RecordField : String -> Type -> Type where
  (:->) : (0 s:String) -> t -> RecordField s t

public export
data FieldSpec : String -> Type -> Type where
  MkFieldSpec : (s:String) -> t -> FieldSpec s t

public export
FieldSpecType : FieldSpec s t -> t
FieldSpecType (MkFieldSpec s t) = t

public export
FieldToType : Type -> Type
FieldToType k = {s:String} -> FieldSpec s k -> Type

public export
data Record : RecordSpec k -> FieldToType k -> Type where
    Nil : {0 f:FieldToType k} -> Record Nil f
    (::) :  {0 lbl:String}
         -> {0 f: FieldToType k}
         -> {0 t: k}
         -> RecordField lbl (f (MkFieldSpec lbl t))
         -> Record xs f
         -> Record ((lbl, t) :: xs) f

-- | Simple record indexed by Types
public export
SimpleRecord : RecordSpec Type -> Type
SimpleRecord s = Record s FieldSpecType

public export
AllConstraints : (a -> Type) -> List a -> Type
AllConstraints f [] = ()
AllConstraints f (c::cs) = (f c, AllConstraints f cs)

public export
OverSpec : (k -> Type) -> (String, k) -> Type
OverSpec c (name, value) = c value

public export
AllSpecs : (k -> Type) -> RecordSpec k -> Type
AllSpecs c = AllConstraints (OverSpec c)

-- proof that the spec has some field with a given type.
public export
data HasField : (s:String) -> (t:k) -> RecordSpec k -> Type where
  [search s]
  FirstField : HasField s t ((s, t) :: _)
  NextField : (0 prf : (t == s) === False) => HasField s v xs -> HasField s v ((t, w) :: xs)
%builtin Natural HasField

implementation Uninhabited (HasField s t []) where
  uninhabited FirstField impossible
  uninhabited NextField impossible

public export
HasField' : RecordSpec k -> (String, k) -> Type
HasField' r (s, t) = HasField s t r

public export
HasFields : (l:RecordSpec k) -> RecordSpec k -> Type
HasFields l r = AllConstraints (HasField' r)  l

public export
data IsNothing : Maybe a -> Type where
  ItIsNothing : IsNothing Nothing

-- proof that an optional field with the given type exists.  The type
-- must be either present with the right type, or be absent.  This is
-- written in terms of HasField, so it is be isomorphic to Maybe
-- Natural, and can use efficient indexing.
public export
data HasOptionalField : (s:String) -> (t:k) -> RecordSpec k -> Type where
  NoSuchField : IsNothing (lookup s specs) => HasOptionalField s t specs
  FieldExists : HasField s t specs => HasOptionalField  s t specs

public export
HasOptionalField' : RecordSpec k -> (String, k) -> Type
HasOptionalField' r (s, t) = HasOptionalField s t r

public export
HasOptionalFields : (l:RecordSpec k) -> RecordSpec k -> Type
HasOptionalFields l r = AllConstraints (HasOptionalField' r)  l

export
remField : RecordSpec k -> (String, k) -> RecordSpec k
remField [] _ = []
remField ((s, k) :: specs) (t, l) = 
  if (s == t) then specs else (s, k) :: remField specs (t, l)

export
remFields :  (l:RecordSpec k)
          -> RecordSpec k 
          -> RecordSpec k
remFields spec [] = spec
remFields spec (x :: xs) = remFields (remField spec x) xs

public export
data NubFields : RecordSpec k -> RecordSpec k -> RecordSpec k ->Type where
  MkNubFields : {spec:RecordSpec k} -> {fields: RecordSpec k} -> NubFields spec fields (remFields spec fields)

public export
data WithRecordFields :  RecordSpec k
                      -> RecordSpec k 
                      -> RecordSpec k
                      -> RecordSpec k 
                      -> Type where
  MkWithRecordFields :  {spec:RecordSpec k} 
                     -> {mandatory: RecordSpec k}
                     -> {optional: RecordSpec k}
                     -> {other: RecordSpec k}
                     -> HasFields spec mandatory
                     => NubFields spec (optional ++ mandatory) other
                     => WithRecordFields spec mandatory optional other

-- RecordFieldType : (l:RecordSpec k) -> (lbl:String) -> ({label:String} -> k -> Type) -> HasField lbl t l  => Type
-- RecordFieldType ((lbl, t) :: _) lbl f @{FirstField} = f {label=lbl} t
-- RecordFieldType (_ :: xs) s f @{NextField x} = RecordFieldType xs s f

export
hasFieldToIndex : HasField s t r -> Integer
hasFieldToIndex FirstField = 0
hasFieldToIndex (NextField prevField) = 1 + hasFieldToIndex prevField
%builtin NaturalToInteger natToInteger

export
get : (0 lbl:String) ->
      {0 f: FieldToType k} ->
      HasField lbl t r => 
      Record r f -> 
      (f (MkFieldSpec lbl t))
get s @{FirstField} ((s :-> x) :: y) = x
get s @{(NextField later)} (_ :: xs) = get s @{later} xs

export
getMaybe : {0 f:FieldToType k} -> (0 s:String) -> HasOptionalField s t r => Record r f -> Maybe (f (MkFieldSpec s t))
getMaybe _ @{NoSuchField} _ = Nothing
getMaybe s @{FieldExists} rl = Just $ get s rl

export
getOpt : {0 f:FieldToType k} -> (0 s:String) -> HasOptionalField s t r => Lazy (f (MkFieldSpec s t)) -> Record r f -> f (MkFieldSpec s t)
getOpt s def r = fromMaybe def $ getMaybe s r

export
mapRecord : {spec : RecordSpec k} -> 
            {0 f:FieldToType k} -> 
            {0 g:FieldToType k} -> 
            ({0 a : k} -> {lbl:String} -> f (MkFieldSpec lbl a) -> g (MkFieldSpec lbl a)) -> 
            Record spec f -> 
            Record spec g
mapRecord h [] = []
mapRecord h ((lbl :-> y) :: z) = (lbl :-> h y) :: mapRecord h z

export
fillRecord : {0 f : FieldToType k} -> (spec:RecordSpec k) -> ({s : String} -> {a : k} -> f (MkFieldSpec s a)) -> Record spec f
fillRecord [] v = []
fillRecord ((s, x) :: xs) v = (s :-> v) :: fillRecord xs v

export
zipWithRecord :  {spec : RecordSpec k} -> 
                 {0 f : FieldToType k} ->
                 {0 g : FieldToType k} ->
                 {0 h : FieldToType k} ->
                 ({a : k} -> {s:String} -> f (MkFieldSpec s a) -> g (MkFieldSpec s a) -> h (MkFieldSpec s a)) ->
                 Record spec f -> 
                 Record spec g -> 
                 Record spec h
zipWithRecord f [] [] = []
zipWithRecord f (s :-> x :: z) (s :-> y :: w) = 
  s :-> f x y :: zipWithRecord f z w

namespace Hkd
  public export
  data HkdList : (k -> Type) -> List k -> Type where
    Nil : HkdList f []
    (::) : {0 f:k -> Type} -> f a -> HkdList f b -> HkdList f (a :: b)

export
mapHkd : {0 g : k -> Type} -> (forall a . f a -> g a) -> HkdList f s -> HkdList g s
mapHkd f [] = []
mapHkd f (x :: y) = f x :: mapHkd f y

export
splitRow : {0 fs : List (FieldToType k)} ->
           {0 as : RecordSpec k} ->
           HkdList (Record ((s, a) :: as)) fs -> 
           ( HkdList ($ MkFieldSpec s a) fs
           , HkdList (Record as) fs)
splitRow [] = ([], [])
splitRow (((s :-> x) :: r) :: y) = 
  let (ls, rs) = splitRow y 
  in (x :: ls, r :: rs)

export
zipWithManyRecord : {0 fs : List (FieldToType k)} ->
                    {g : FieldToType k} -> 
                    {spec : RecordSpec k} ->
                    ({s : String} -> {a : k} -> Hkd.HkdList ($ MkFieldSpec s a) fs -> g (MkFieldSpec s a)) ->
                    Hkd.HkdList (Record spec) fs -> 
                    Record spec g
zipWithManyRecord f l with (spec)
  _ | Nil = []
  _ | ((s1, a1)::ss) =
      let (l1, ls) = splitRow l
      in s1 :-> f l1 :: zipWithManyRecord f ls

export      
foldMapRecord : Monoid m =>
                {spec : RecordSpec k} ->
                {f : FieldToType k} ->
                ({s:String} -> {a : k} -> f (MkFieldSpec s a) -> m) -> 
                Record spec f -> 
                m
foldMapRecord f [] = neutral
foldMapRecord f ((s :-> x) :: y) = f x <+> foldMapRecord f y

export
foldrRecord : {f : FieldToType k} -> 
              {spec : RecordSpec k} ->
               ({s : String} -> {a : k} -> f (MkFieldSpec s a) -> acc -> acc) -> 
               acc -> 
               Record spec f -> 
               acc
foldrRecord f acc [] = acc
foldrRecord f acc ((s :-> x) :: y) =  f x $ foldrRecord f acc y

export
foldlRecord : {f : FieldToType k} -> 
              {spec : RecordSpec k} -> 
              ({s : String} -> {a : k} -> acc -> f (MkFieldSpec s a) -> acc) -> 
              acc -> 
              Record spec f -> 
              acc
foldlRecord f acc [] = acc
foldlRecord f acc ((s :-> x) :: y) = foldlRecord f (f acc x) y

export
recordLabels : {spec : RecordSpec k} -> Record spec (const String)
recordLabels {spec = []} = []
recordLabels {spec = ((lbl, x) :: xs)} = (lbl :-> lbl) :: recordLabels {spec = xs}

public export
EntryDict : ((String, k) -> Type) -> FieldToType k
EntryDict c (MkFieldSpec s t) = c (s, t)

export
recordDicts : (0 c : (String, k) -> Type) -> 
              (spec : RecordSpec k) -> 
              (cs : AllConstraints c spec) => 
              Record spec (EntryDict c)
recordDicts c [] = []
recordDicts c ((s, t) :: xs) {cs=(c1,_)} = s :-> c1 :: recordDicts c xs

export
recordSpecs : (l : RecordSpec k) -> Record l (const k)
recordSpecs [] = []
recordSpecs ((s, spec) :: xs) = s :-> spec :: recordSpecs xs

export
appendRecords : {spec1 : RecordSpec k} ->
                {spec2 : RecordSpec k} -> 
                {f : FieldToType k} ->
                Record spec1 f -> 
                Record spec2 f -> 
                Record (spec1 ++ spec2) f
appendRecords [] y = y
appendRecords (x :: z) y = x :: appendRecords z y

