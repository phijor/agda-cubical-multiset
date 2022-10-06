module Multiset.Util.Sigma where

open import Multiset.Prelude

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma as Sigma
  using (_×_)

private
  variable
    ℓ ℓ' : Level
    A A' : Type ℓ
    B B' : (a : A) → Type ℓ'

Σ-cong-equiv-snd : (∀ a → B a ≃ B' a)
  → Σ A B ≃ Σ A B'
Σ-cong-equiv-snd {A = A} {B = B} {B' = B'} h = fun , isEquivFun where
  fun : Σ A B → Σ A B'
  fun (a , b) = a , equivFun (h a) b

  isEquivFun : isEquiv fun
  equiv-proof isEquivFun (a , b') = ctr , isCtr where
    _ = {! equivCtr (h a) !}

    h-fiber : (b' : B' a) → fiber (equivFun (h a)) b'
    h-fiber b' = equivCtr (h a) b'

    h⁻¹[_] : B' a → B a
    h⁻¹[ b' ] = h-fiber b' .fst

    h⁻¹[_]-Path : (b' : B' a) → equivFun (h a) h⁻¹[ b' ] ≡ b'
    h⁻¹[ b' ]-Path = h-fiber b' .snd

    ctr : fiber fun (a , b')
    ctr = (a , h⁻¹[ b' ]) , Sigma.ΣPathP (refl , h⁻¹[ b' ]-Path)

    isCtr : (y : fiber fun (a , b')) → ctr ≡ y
    isCtr ((a' , b'') , p) = Sigma.ΣPathP (Sigma.ΣPathP (a≡a' , {! !}) , {! !}) where
      _ : fun (a' , b'') ≡ (a , b')
      _ = p

      a≡a' : a ≡ a'
      a≡a' = sym (cong fst p)

      h[b'']≡b' : PathP (λ i → B' (a≡a' i)) b' (equivFun (h a') b'')
      h[b'']≡b' = cong snd (sym p)

      b-Path : PathP (λ i → B (a≡a' i)) h⁻¹[ b' ] b''
      b-Path = {!congP (λ i → h⁻¹[_]) h[b'']≡b' !}

Σ-cong-equiv : (e : A ≃ A')
  → ((x : A) → B x ≃ B' (equivFun e x))
  → Σ A B ≃ Σ A' B'
Σ-cong-equiv e e' = compEquiv (Σ-cong-equiv-snd e') (Sigma.Σ-cong-equiv-fst e)
