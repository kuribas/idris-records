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
infixr 10 :->:
infixr 10 !!

||| Specification for a record, consisting of a list of key value pairs, where the value is the specification for that field.
public export
RecordSpec : Type -> Type
RecordSpec k = List (String, k)

||| A field (label value pair) in the record, with the given label and type.  The label is erased at the value level, but included for program clarity.
public export
data RecordField : String -> Type -> Type where
  (:->) : (0 s:String) -> t -> RecordField s t

||| A field definition for a given label.
public export
data Field : String -> Type -> Type where
  (:->:) : (s:String) -> t -> Field s t

||| Get the specification for a single field.
public export
FieldSpec : Field s t -> t
FieldSpec (s :->: t) = t

||| The type of a field.
public export
FieldToType : Type -> Type
FieldToType k = {s:String} -> Field s k -> Type

||| A strongly specified record.  The type contains the specification, and a function mapping each that specification for each field to a concrete type.
public export
data Record : RecordSpec k -> FieldToType k -> Type where
    Nil : {0 f:FieldToType k} -> Record Nil f
    (::) :  {0 lbl:String}
         -> {0 f: FieldToType k}
         -> {0 t: k}
         -> RecordField lbl (f (lbl :->: t))
         -> Record xs f
         -> Record ((lbl, t) :: xs) f

||| Simple record with types as specification
public export
SimpleRecord : RecordSpec Type -> Type
SimpleRecord s = Record s FieldSpec

||| Constraint that holds for all values in a list.
public export
AllConstraints : (a -> Type) -> List a -> Type
AllConstraints f [] = ()
AllConstraints f (c::cs) = (f c, AllConstraints f cs)

||| proof that the spec has some label with the given spec
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

||| Proof that a spec is a subset of another spec.
public export
HasFields : (l:RecordSpec k) -> RecordSpec k -> Type
HasFields l r = AllConstraints (HasField' r)  l

||| A label of a spec.  Contains an automatic proof that the label is actually in the spec.
public export
data LabelOf : RecordSpec k -> Type where
  MkLabel : {0 spec : RecordSpec k} ->
            (lbl : String) -> 
            {t : k} ->
            HasField lbl t spec =>
            LabelOf spec

||| Extract the string of the label
export
labelString : LabelOf spec -> String
labelString (MkLabel lbl) = lbl

||| Extract the spec from the label
export
labelSpec : {0 spec : RecordSpec k} -> LabelOf spec -> k
labelSpec (MkLabel {t=t} _) = t

public export
data IsNothing : Maybe a -> Type where
  ItIsNothing : IsNothing Nothing

||| proof that an optional field with the given spec exists.  The spec
||| must be either present with the right type, or be absent.  This is
||| written in terms of HasField, so it is isomorphic to Maybe
||| Natural, which has a more efficient representation.
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

-- RecordFieldSpec : (l:RecordSpec k) -> (lbl:String) -> ({label:String} -> k -> Type) -> HasField lbl t l  => Type
-- RecordFieldSpec ((lbl, t) :: _) lbl f @{FirstField} = f {label=lbl} t
-- RecordFieldSpec (_ :: xs) s f @{NextField x} = RecordFieldSpec xs s f

export
hasFieldToIndex : HasField s t r -> Integer
hasFieldToIndex FirstField = 0
hasFieldToIndex (NextField prevField) = 1 + hasFieldToIndex prevField
%builtin NaturalToInteger natToInteger

public export
get : (0 lbl:String) ->
      {0 f: FieldToType k} ->
      HasField lbl t r => 
      Record r f -> 
      (f (lbl :->: t))
get s @{FirstField} ((s :-> x) :: y) = x
get s @{(NextField later)} (_ :: xs) = get s @{later} xs

public export
SpecGet : (0 lbl:String) ->
          (r : RecordSpec k) ->
          {t:k} ->
          HasField lbl t r => 
          k
SpecGet lbl ((lbl, t) :: _) @{FirstField} = t
SpecGet lbl ((t, w) :: xs) @{(NextField x)} = SpecGet lbl xs

export 
(!!) : {0 f: FieldToType k} ->
       Record r f ->
       (0 lbl:String) ->
       HasField lbl t r => 
       (f (lbl :->: t))
r !! s = get s r

public export
getMaybe : {0 f:FieldToType k} -> (0 s:String) -> HasOptionalField s t r => Record r f -> Maybe (f (s :->: t))
getMaybe _ @{NoSuchField} _ = Nothing
getMaybe s @{FieldExists} rl = Just $ get s rl

public export
getOpt : {0 f:FieldToType k} -> (0 s:String) -> HasOptionalField s t r => Lazy (f (s :->: t)) -> Record r f -> f (s :->: t)
getOpt s def r = fromMaybe def $ getMaybe s r

export
set : {0 f: FieldToType k} ->
      {0 t : k} -> 
      {0 lbl : String} ->
      RecordField lbl (f (lbl :->: t)) ->
      HasField lbl t r => 
      Record r f -> 
      Record r f
set (lbl :-> x) @{FirstField} (lbl :-> _ :: r) = (lbl :-> x) :: r
set x @{(NextField nf)} (y :: z) = y :: set x z

public export
mapRecord : {specs : RecordSpec k} -> 
            {0 f:FieldToType k} -> 
            {0 g:FieldToType k} -> 
            ({lbl:String} -> {spec : k} -> f (lbl :->: spec) -> g (lbl :->: spec)) -> 
            Record specs f -> 
            Record specs g
mapRecord h [] = []
mapRecord h ((lbl :-> y) :: z) = (lbl :-> h y) :: mapRecord h z

public export
sequenceRecord : Applicative m =>
                 {spec : RecordSpec k} -> 
                 {0 f:FieldToType k} -> 
                 Record spec (m . f) ->
                 m (Record spec f)
sequenceRecord [] = pure []
sequenceRecord ((lbl :-> x) :: y) =
  (\x', xs' => lbl :-> x' :: xs') <$> x <*> sequenceRecord y

public export 
traverseRecord : Applicative m =>
                 {specs : RecordSpec k} -> 
                 {0 f:FieldToType k} -> 
                 {0 g:FieldToType k} -> 
                 ({lbl : String} -> 
                  {spec : k} -> 
                  f (lbl :->: spec) ->
                  m (g (lbl :->: spec))) ->
                 Record specs f ->
                 m (Record specs g)
traverseRecord f [] = pure []
traverseRecord f ((lbl :-> x) :: y) = 
  (\x', xs' => lbl :-> x' :: xs') <$> f x <*> traverseRecord f y

-- | convenient specialization of sequenceRecord, to bind applicative values.
public export
aseq : Applicative m =>
       {spec : RecordSpec Type} -> 
       Record spec (m . FieldSpec) -> 
       m (SimpleRecord spec)
aseq = sequenceRecord


public export
mapRecordSpec : {0 f : FieldToType k} -> 
                (spec:RecordSpec k) ->
                ((label:String) -> (spec:k) -> f (label :->: spec)) -> 
                Record spec f
mapRecordSpec [] v = []
mapRecordSpec ((s, x) :: xs) v = (s :-> v s x) :: mapRecordSpec xs v

public export
traverseRecordSpec : Applicative m =>
                     {0 f : FieldToType k} -> 
                     (spec:RecordSpec k) ->
                     ((label:String) -> (spec:k) -> m (f (label :->: spec))) -> 
                     m (Record spec f)
traverseRecordSpec [] _ = pure []
traverseRecordSpec ((s, x) :: xs) f = 
  (\x, xs => (s :-> x) :: xs) <$> f s x <*>  traverseRecordSpec xs f

public export
zipWithRecord :  {spec : RecordSpec k} -> 
                 {0 f : FieldToType k} ->
                 {0 g : FieldToType k} ->
                 {0 h : FieldToType k} ->
                 ({s:String} -> {a : k} -> f (s :->: a) -> g (s :->: a) -> h (s :->: a)) ->
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
           ( HkdList ($ s :->: a) fs
           , HkdList (Record as) fs)
splitRow [] = ([], [])
splitRow (((s :-> x) :: r) :: y) = 
  let (ls, rs) = splitRow y 
  in (x :: ls, r :: rs)

export
zipWithManyRecord : {0 fs : List (FieldToType k)} ->
                    {g : FieldToType k} -> 
                    {spec : RecordSpec k} ->
                    ({s : String} -> {a : k} -> Hkd.HkdList ($ s :->: a) fs -> g (s :->: a)) ->
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
                ({s:String} -> {a : k} -> f (s :->: a) -> m) -> 
                Record spec f -> 
                m
foldMapRecord f [] = neutral
foldMapRecord f ((s :-> x) :: y) = f x <+> foldMapRecord f y

export
foldrRecord : {f : FieldToType k} -> 
              {spec : RecordSpec k} ->
               ({s : String} -> {a : k} -> f (s :->: a) -> acc -> acc) -> 
               acc -> 
               Record spec f -> 
               acc
foldrRecord f acc [] = acc
foldrRecord f acc ((s :-> x) :: y) =  f x $ foldrRecord f acc y

export
foldlRecord : {f : FieldToType k} -> 
              {spec : RecordSpec k} -> 
              ({s : String} -> {a : k} -> acc -> f (s :->: a) -> acc) -> 
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
EntryDict c (s :->: t) = c (s, t)

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

public export
RecordSubset : {spec : RecordSpec k} -> 
               List (LabelOf spec) ->
               RecordSpec k
RecordSubset [] = []
RecordSubset {spec} ((MkLabel {t} lbl) :: xs) =
  (lbl, t) :: RecordSubset xs

export
recordSubset : {spec : RecordSpec k} -> 
               {f : FieldToType k} ->
               (labels : List (LabelOf spec)) ->
               Record spec f ->
               Record (RecordSubset labels) f
recordSubset [] r = []
recordSubset ((MkLabel lbl) :: xs) r = 
  (lbl :-> get lbl r) :: recordSubset xs r
