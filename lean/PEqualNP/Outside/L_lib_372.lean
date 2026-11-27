import PEqualNP.Defs

-- Method: the forced bits are built by well-founded recursion on the forced index (`forcedBits`),
-- each one read off `rule` from the seed and the bits already built; `Fin.append` glues seed and forced bits.
-- Uniqueness is strong induction on the forced index; the Equiv's inverse reads the free head,
-- so `Nat.card_congr` gives 2 ^ free. Header and `_aux` namespace shape follow L_lib_370 (PR #22222).

namespace PEqualNP.Outside.L_lib_372_aux

/-- The forced bits determined by `rule` from the free head `seed`, indexed by `ℕ` (junk past `forced`). -/
def forcedBits {free forced : ℕ}
    (rule : (i : Fin forced) → (Fin free → Bool) → (Fin i.val → Bool) → Bool)
    (seed : Fin free → Bool) (n : ℕ) : Bool :=
  if h : n < forced then rule ⟨n, h⟩ seed (fun j => forcedBits rule seed j.val) else false
termination_by n
decreasing_by exact j.isLt

theorem forcedBits_spec {free forced : ℕ}
    (rule : (i : Fin forced) → (Fin free → Bool) → (Fin i.val → Bool) → Bool)
    (seed : Fin free → Bool) (i : Fin forced) :
    forcedBits rule seed i.val = rule i seed (fun j => forcedBits rule seed j.val) := by
  rw [forcedBits]; simp [i.isLt]

end PEqualNP.Outside.L_lib_372_aux

open PEqualNP.Outside.L_lib_372_aux in
theorem PEqualNP.Outside.L_lib_372 :
    ∀ (free forced : ℕ)
  (rule : (i : Fin forced) → (Fin free → Bool) → (Fin i.val → Bool) → Bool),
  let freeBits := fun (word : Fin (free + forced) → Bool) (a : Fin free) =>
    word (Fin.castAdd forced a)
  let passes := fun (word : Fin (free + forced) → Bool) =>
    ∀ i : Fin forced, word (Fin.natAdd free i) =
      rule i (freeBits word)
        (fun j => word (Fin.natAdd free (Fin.castLE (Nat.le_of_lt i.isLt) j)))
  ∃ complete : (Fin free → Bool) ≃ { word // passes word },
    (∀ seed word, freeBits word.val = seed ↔ word = complete seed) ∧
    Nat.card { word // passes word } = 2 ^ free := by
  intro free forced rule
  dsimp only
  -- the completion of a seed
  have hpass : ∀ seed : Fin free → Bool,
      ∀ i : Fin forced,
        Fin.append seed (fun k : Fin forced => forcedBits rule seed k.val) (Fin.natAdd free i) =
        rule i (fun a => Fin.append seed (fun k : Fin forced => forcedBits rule seed k.val)
            (Fin.castAdd forced a))
          (fun j => Fin.append seed (fun k : Fin forced => forcedBits rule seed k.val)
            (Fin.natAdd free (Fin.castLE (Nat.le_of_lt i.isLt) j))) := by
    intro seed i
    simp only [Fin.append_left, Fin.append_right, Fin.val_castLE]
    exact forcedBits_spec rule seed i
  -- uniqueness: a passing word with free head `seed` is the completion of `seed`
  have huniq : ∀ (seed : Fin free → Bool) (word : Fin (free + forced) → Bool),
      (∀ i : Fin forced, word (Fin.natAdd free i) =
        rule i (fun a => word (Fin.castAdd forced a))
          (fun j => word (Fin.natAdd free (Fin.castLE (Nat.le_of_lt i.isLt) j)))) →
      (fun a => word (Fin.castAdd forced a)) = seed →
      word = Fin.append seed (fun k : Fin forced => forcedBits rule seed k.val) := by
    intro seed word hw hs
    have key : ∀ n (h : n < forced), word (Fin.natAdd free ⟨n, h⟩) = forcedBits rule seed n := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro h
        rw [hw ⟨n, h⟩, hs, forcedBits_spec rule seed ⟨n, h⟩]
        congr 1
        funext j
        exact ih j.val j.isLt (lt_trans j.isLt h)
    funext x
    refine Fin.addCases (fun a => ?_) (fun k => ?_) x
    · rw [Fin.append_left, ← hs]
    · rw [Fin.append_right]
      exact key k.val k.isLt
  let complete : (Fin free → Bool) ≃ { word : Fin (free + forced) → Bool //
      ∀ i : Fin forced, word (Fin.natAdd free i) =
        rule i (fun a => word (Fin.castAdd forced a))
          (fun j => word (Fin.natAdd free (Fin.castLE (Nat.le_of_lt i.isLt) j))) } :=
    { toFun := fun seed => ⟨Fin.append seed (fun k : Fin forced => forcedBits rule seed k.val),
        hpass seed⟩
      invFun := fun w a => w.val (Fin.castAdd forced a)
      left_inv := fun seed => by funext a; simp only [Fin.append_left]
      right_inv := fun w => by
        apply Subtype.ext
        exact (huniq _ w.val w.property rfl).symm }
  refine ⟨complete, fun seed word => ?_, ?_⟩
  · constructor
    · intro hs
      exact Subtype.ext (huniq seed word.val word.property hs)
    · rintro rfl
      funext a
      simp only [complete, Equiv.coe_fn_mk, Fin.append_left]
  · rw [← Nat.card_congr complete]
    simp
