import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20666_aux

open PEqualNP.CircuitLowerBounds

def mkG (c : Bool × ℕ × ℕ) : Gate := ⟨bif c.1 then GateOp.or else GateOp.and, [c.2.1, c.2.2]⟩

def stepB (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

/-- One step on packed wires: one number per wire, one bit per input. -/
def stepN (w : List ℕ) (c : Bool × ℕ × ℕ) : List ℕ :=
  w ++ [bif c.1 then w.getD c.2.1 0 ||| w.getD c.2.2 0 else w.getD c.2.1 0 &&& w.getD c.2.2 0]

theorem getD_map (l : List ℕ) (k i : ℕ) :
    (l.map fun a => a.testBit k).getD i false = (l.getD i 0).testBit k := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? with
  | none => exact (Nat.zero_testBit k).symm
  | some a => rfl

theorem fold_eq (k : ℕ) : ∀ (code : List (Bool × ℕ × ℕ)) (l : List ℕ),
    (code.map mkG).foldl stepB (l.map fun a => a.testBit k) =
      (code.foldl stepN l).map fun a => a.testBit k
  | [], _ => rfl
  | (o, a, b) :: code, l => by
    have h : stepB (l.map fun a => a.testBit k) (mkG (o, a, b)) =
        (stepN l (o, a, b)).map fun a => a.testBit k := by
      cases o <;>
        simp only [stepB, stepN, mkG, Bool.cond_true, Bool.cond_false, GateOp.eval, List.map_cons, List.map_nil,
          List.all_cons, List.all_nil, List.any_cons, List.any_nil, id, Bool.and_true, Bool.or_false,
          getD_map, List.map_append, Nat.testBit_and, Nat.testBit_or]
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, h]
    exact fold_eq k code _

theorem eval_eq (code : List (Bool × ℕ × ℕ)) (out k : ℕ) (l : List ℕ) :
    (⟨code.map mkG, out⟩ : Circuit).eval (l.map fun a => a.testBit k) =
      ((code.foldl stepN l).getD out 0).testBit k :=
  (congrArg (fun w => w.getD out false) (fold_eq k code l)).trans (getD_map _ k out)

/-- The packed run decides the circuit: `T` is the packed table of `f`. -/

theorem mono (code : List (Bool × ℕ × ℕ)) (out : ℕ) :
    PEqualNP.MetaComplexity.Monotone2 ⟨code.map mkG, out⟩ := fun g hg => by
  obtain ⟨c, -, rfl⟩ := List.mem_map.mp hg
  match c with
  | (true, a, b) => exact ⟨Or.inr rfl, Nat.le_refl 2⟩
  | (false, a, b) => exact ⟨Or.inl rfl, Nat.le_refl 2⟩

/-- Pair `(u, v)` is bit `u * m + v` of every column. -/
theorem rep (n m : ℕ) (code : List (Bool × ℕ × ℕ)) (out : ℕ) (A : Fin n → Fin m → Bool) (cols : List ℕ) (T : ℕ)
    (hc : ∀ (u : Fin n) (v : Fin m),
      PEqualNP.Represents.oneEach u v = cols.map fun a => a.testBit (u.val * m + v.val))
    (hT : ∀ (u : Fin n) (v : Fin m), T.testBit (u.val * m + v.val) = A u v)
    (h : (code.foldl stepN cols).getD out 0 = T) :
    PEqualNP.Represents.Represents A ⟨code.map mkG, out⟩ := fun u v => by
  rw [hc u v, eval_eq, h]; exact hT u v

end PEqualNP.Outside.L_meta_20666_aux

theorem PEqualNP.Outside.L_meta_20666 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (16188416 : ℕ).testBit (5 * u.val + v.val)) 7 := by
  exact ⟨⟨[(true, 2, 4), (false, 10, 5), (true, 4, 3), (true, 6, 7), (true, 13, 8), (false, 14, 12), (true, 15, 11)].map PEqualNP.Outside.L_meta_20666_aux.mkG, 16⟩, PEqualNP.Outside.L_meta_20666_aux.mono _ _, by decide,
    PEqualNP.Outside.L_meta_20666_aux.rep 5 5 _ _ _ [31, 992, 31744, 1015808, 32505856, 1082401, 2164802, 4329604, 8659208, 17318416] 16188416
      (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩
