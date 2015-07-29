{-# OPTIONS --universe-polymorphism #-}
module Ornament where

open import Data.Nat using (ℕ)
open import Data.Fin 
open import Data.Bool
open import Data.Product
open import Data.Unit
open import Data.List

infix 4 _≡_

data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

--

-- Modified from Conor's original HOAS presentation

data IndexParam {n} (I : Set) (N : Fin n) : Set₁ where
  -- read an indexed subnote; continue
  rec : I -> IndexParam I N -> IndexParam I N

  -- stop and return the node's index
  ret : I -> IndexParam I N

semantics : ∀{I} -> ∀{n : ℕ} -> IndexParam I (fromℕ n) -> (I -> Set) -> I -> Set
semantics = {!!}
  
record EmbedDataConstr : Set₁ where
  constructor embedDataConstr
  field arityTyping : {!!}

record EmbedDataTy (I A : Set) : Set₁ where
  constructor embedDataTy
  field indexes : List I
  field parameters : List A
  field constrs : List EmbedDataConstr

data Desc (I : Set) : Set₁ where
  -- read field in A; continue, given its value
  -- I don't think this is really what we want -- want parametricity
  arg : (a : Set) -> (a -> Desc I) -> Desc I

  -- read an indexed subnode; continue regardless
  rec : I -> Desc I -> Desc I

  -- stop reading and return the node’s index
  ret : I -> Desc I

  -- choice between n different constructors
  choice : (n : ℕ) -> (Fin n -> Desc I) -> Desc I

-- The semantics ("extension") of an indexed container
⟦_⟧ : ∀{I} -> Desc I -> (I -> Set) -> I -> Set
⟦ arg A D ⟧ R i = Σ A λ a → ⟦ D a ⟧ R i
⟦ rec h D ⟧ R i = R h × ⟦ D ⟧ R i
⟦ ret o ⟧ R i = o ≡ i
⟦ choice n D ⟧ R i =  Σ (Fin n) λ #n -> ⟦ D #n ⟧ R i


-- This is really the least fixpoint operator
data Data {I}(D : Desc I)(i : I) : Set where
  ⟨_⟩ : ⟦ D ⟧ (Data D) i -> Data D i

-- TODO think about codata / greatest fixed point
-- data CoData {I}(D : Desc I)(i : I) : Set where
--   ⟩_⟨ : 

--


record DataConstr : Set where
  constructor dataConstr
  field arityTyping : {!!}

record DataTy : Set where
  constructor dataTy
  field indexes : List ℕ
  field parameters : List ℕ
  field constrs : List {!!}

--

NatChoiceDesc : Desc ⊤
NatChoiceDesc = choice 2 λ
  { zero -> ret tt
  ; (suc n) -> rec tt (ret tt)
  }

NatChoice : Set
NatChoice = Data NatChoiceDesc tt

zeChoice : NatChoice
zeChoice = ⟨ zero , refl ⟩

suChoice : NatChoice -> NatChoice
suChoice n = ⟨ suc zero , n , refl ⟩

--

NatDesc : Desc ⊤
NatDesc = arg Bool λ
  { true -> ret tt
  ; false -> rec tt (ret tt)
  }

Nat : Set
Nat = Data NatDesc tt

ze : Nat
ze = ⟨ true , refl ⟩

su : Nat -> Nat
su n = ⟨ false , n , refl ⟩

--

VecDesc : Set -> Desc Nat
VecDesc X = arg Bool λ
  { false -> ret ze
  ; true -> arg X λ _ -> arg Nat λ n -> rec n (ret (su n))
  }

Vec : Set -> Nat -> Set
Vec X n = Data (VecDesc X) n

nil : ∀{X} -> Vec X ze
nil = ⟨ false , refl ⟩

cons : ∀{X} -> (n : Nat) -> X -> Vec X n -> Vec X (su n)
cons n x xs = ⟨ true , x , n , xs , refl ⟩
