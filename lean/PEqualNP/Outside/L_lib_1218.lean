import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1218

section Inlined

namespace Parent

abbrev Tip (m : ℕ) := Fin m × Bool

noncomputable def livePairs {m : ℕ} (on : Fin m → Bool) : Finset (Fin m) :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  Finset.univ.filter (fun i => on i)

noncomputable def liveTips {m : ℕ} (on : Fin m → Bool) : Finset (Tip m) :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  Finset.univ.filter (fun p => on p.1)

def IsCover {m : ℕ} (nb : Tip m → Finset (Tip m))
    (on : Fin m → Bool) (C : Finset (Tip m)) : Prop :=
  C ⊆ liveTips on ∧
  ∀ p ∈ liveTips on, ∀ r ∈ nb p, r ∈ liveTips on → p ∈ C ∨ r ∈ C

open Classical in
noncomputable def minima {m : ℕ} (nb : Tip m → Finset (Tip m))
    (on : Fin m → Bool) : Finset (Finset (Tip m)) :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  Finset.univ.filter (fun C => IsCover nb on C ∧ ∀ W, IsCover nb on W → C.card ≤ W.card)

@[simp] theorem mem_minima {m : ℕ} {nb : Tip m → Finset (Tip m)}
    {on : Fin m → Bool} {C : Finset (Tip m)} :
    C ∈ minima nb on ↔ IsCover nb on C ∧ ∀ W, IsCover nb on W → C.card ≤ W.card := by
  simp [minima]

noncomputable def selected {m : ℕ} (on f : Fin m → Bool) : Finset (Tip m) :=
  (livePairs on).image (fun i => (i, !(f i)))

@[simp] theorem mem_selected {m : ℕ} {on f : Fin m → Bool} {i : Fin m} {b : Bool} :
    (i,b) ∈ selected on f ↔ on i = true ∧ !(f i) = b := by
  cases b <;> cases hb : f i <;> simp [selected, livePairs, hb]

@[simp] theorem card_selected {m : ℕ} (on f : Fin m → Bool) :
    (selected on f).card = (livePairs on).card :=
  Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)

def readCover {m : ℕ} (C : Finset (Tip m)) (i : Fin m) : Bool :=
  decide ((i,false) ∈ C)

theorem selected_read_subset {m : ℕ} {nb : Tip m → Finset (Tip m)}
    {on : Fin m → Bool} (matchEdge : ∀ i, (i,true) ∈ nb (i,false))
    {C : Finset (Tip m)} (hC : IsCover nb on C) :
    selected on (readCover C) ⊆ C := by
  rintro ⟨i,b⟩ h
  obtain ⟨hi, hb⟩ := mem_selected.mp h
  have hm := hC.2 (i,false) (by simp [liveTips,hi]) (i,true) (matchEdge i)
      (by simp [liveTips,hi])
  by_cases hf : (i,false) ∈ C <;> simp_all [readCover]

theorem cover_lower {m : ℕ} {nb : Tip m → Finset (Tip m)} {on : Fin m → Bool}
    (matchEdge : ∀ i, (i,true) ∈ nb (i,false)) {C : Finset (Tip m)}
    (hC : IsCover nb on C) : (livePairs on).card ≤ C.card := by
  simpa using Finset.card_le_card (selected_read_subset matchEdge hC)

theorem shore_cover {m : ℕ} {nb : Tip m → Finset (Tip m)} {on : Fin m → Bool}
    (bip : ∀ p, ∀ r ∈ nb p, p.2 ≠ r.2) :
    IsCover nb on (selected on fun _ => false) := by
  constructor
  · rintro ⟨i,b⟩ h
    simpa [liveTips] using (mem_selected.mp h).1
  · rintro ⟨i,b⟩ hi ⟨j,c⟩ he hj
    have hbc := bip (i,b) (j,c) he
    cases b <;> cases c <;> simp_all [liveTips]

theorem cover_optimum {m : ℕ} {nb : Tip m → Finset (Tip m)} {on : Fin m → Bool}
    (bip : ∀ p, ∀ r ∈ nb p, p.2 ≠ r.2)
    (matchEdge : ∀ i, (i,true) ∈ nb (i,false)) :
    (minima nb on).Nonempty ∧ ∀ C ∈ minima nb on, C.card = (livePairs on).card := by
  classical
  have hs := shore_cover (on := on) bip
  constructor
  · refine ⟨_, mem_minima.mpr ⟨hs, ?_⟩⟩
    intro W hW
    simpa using cover_lower matchEdge hW
  · intro C hC
    obtain ⟨hc,hle⟩ := (mem_minima.mp hC)
    exact le_antisymm (by simpa using hle _ hs) (cover_lower matchEdge hc)

def Admissible {m : ℕ} (nb : Tip m → Finset (Tip m)) (on f : Fin m → Bool) : Prop :=
  (∀ i, on i = false → f i = false) ∧
  ∀ i j, on i = true → on j = true → (j,false) ∈ nb (i,true) → f i = true → f j = true

theorem selected_cover_iff {m : ℕ} {nb : Tip m → Finset (Tip m)}
    {on f : Fin m → Bool} (sym : ∀ p r, r ∈ nb p ↔ p ∈ nb r)
    (bip : ∀ p, ∀ r ∈ nb p, p.2 ≠ r.2) :
    IsCover nb on (selected on f) ↔
      ∀ i j, on i = true → on j = true → (j,false) ∈ nb (i,true) → f i = true → f j = true := by
  constructor
  · intro hc i j hi hj he hfi
    have h := hc.2 (i,true) (by simp [liveTips,hi]) (j,false) he (by simp [liveTips,hj])
    simpa [hi, hj, hfi] using h
  · intro h
    refine ⟨?_, ?_⟩
    · rintro ⟨i,b⟩ hi
      simpa [liveTips] using (mem_selected.mp hi).1
    · rintro ⟨i,b⟩ hi ⟨j,c⟩ he hj
      have hbc := bip (i,b) (j,c) he
      have hi' : on i = true := by simpa [liveTips] using hi
      have hj' : on j = true := by simpa [liveTips] using hj
      cases b <;> cases c
      · exact (hbc rfl).elim
      · have hji := h j i hj' hi' ((sym _ _).mp he)
        cases hfi : f i <;> cases hfj : f j <;> simp [hi', hj', hfi, hfj] at *
      · have hij := h i j hi' hj' he
        cases hfi : f i <;> cases hfj : f j <;> simp [hi', hj', hfi, hfj] at *
      · exact (hbc rfl).elim

open Classical in
theorem count_minima {m : ℕ} {nb : Tip m → Finset (Tip m)} {on : Fin m → Bool}
    (sym : ∀ p r, r ∈ nb p ↔ p ∈ nb r) (bip : ∀ p, ∀ r ∈ nb p, p.2 ≠ r.2)
    (matchEdge : ∀ i, (i,true) ∈ nb (i,false)) :
    (minima nb on).card = (Finset.univ.filter (Admissible nb on)).card := by
  classical
  have hopt := (cover_optimum (on := on) bip matchEdge).2
  have hinv : ∀ C ∈ minima nb on, selected on (readCover C) = C := by
    intro C hC
    apply Finset.eq_of_subset_of_card_le
    · exact selected_read_subset matchEdge (mem_minima.mp hC).1
    · simpa using (hopt C hC).le
  symm
  apply Finset.card_bij (fun f _ => selected on f)
  · intro f hf
    obtain ⟨_, h⟩ := (Finset.mem_filter.mp hf).2
    refine mem_minima.mpr ⟨(selected_cover_iff sym bip).2 h, ?_⟩
    intro W hW
    simpa using cover_lower matchEdge hW
  · intro f hf g hg hfg
    funext i
    cases hi : on i
    · rw [(Finset.mem_filter.mp hf).2.1 i hi, (Finset.mem_filter.mp hg).2.1 i hi]
    · have hm : (i,false) ∈ selected on f ↔ (i,false) ∈ selected on g := by rw [hfg]
      cases hfi : f i <;> cases hgi : g i <;> simp [hi, hfi, hgi] at hm ⊢
  · intro C hC
    refine ⟨readCover C, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩, hinv C hC⟩
    · intro i hi
      have hs := (mem_minima.mp hC).1.1
      have hn : (i,false) ∉ C := by
        intro hc
        simpa [liveTips, hi] using hs hc
      simp [readCover, hn]
    · apply (selected_cover_iff sym bip).1
      rw [hinv C hC]
      exact (mem_minima.mp hC).1

def neighborhood {m : ℕ} (out incoming : Fin m → Finset (Fin m)) :
    Tip m → Finset (Tip m)
  | (i,true) => insert (i,false) ((out i).image fun j => (j,false))
  | (i,false) => insert (i,true) ((incoming i).image fun j => (j,true))

theorem neighborhood_properties {m : ℕ} (out incoming : Fin m → Finset (Fin m))
    (transpose : ∀ i j, j ∈ out i ↔ i ∈ incoming j)
    (dout : ∀ i, (out i).card ≤ 2) (din : ∀ i, (incoming i).card ≤ 2) :
    (∀ p, p ∉ neighborhood out incoming p ∧ (neighborhood out incoming p).card ≤ 3) ∧
    (∀ p r, r ∈ neighborhood out incoming p ↔ p ∈ neighborhood out incoming r) ∧
    (∀ p, ∀ r ∈ neighborhood out incoming p, p.2 ≠ r.2) ∧
    (∀ i, (i,true) ∈ neighborhood out incoming (i,false)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨i,b⟩
    cases b
    · refine ⟨by simp [neighborhood], ?_⟩
      exact (Finset.card_insert_le ..).trans
        (Nat.succ_le_succ (Finset.card_image_le.trans (din i)))
    · refine ⟨by simp [neighborhood], ?_⟩
      exact (Finset.card_insert_le ..).trans
        (Nat.succ_le_succ (Finset.card_image_le.trans (dout i)))
  · rintro ⟨i,b⟩ ⟨j,c⟩
    cases b <;> cases c <;> simp [neighborhood, transpose, eq_comm]
  · rintro ⟨i,b⟩ ⟨j,c⟩ hr
    cases b <;> cases c <;> simp_all [neighborhood]
  · intro i
    simp [neighborhood]

def Models {m : ℕ} (out : Fin m → Finset (Fin m)) (on f : Fin m → Bool) : Prop :=
  (∀ i, on i = false → f i = false) ∧
  ∀ i j, on i = true → on j = true → j ∈ out i → f i = true → f j = true

theorem admissible_neighborhood {m : ℕ} (out incoming : Fin m → Finset (Fin m))
    (on f : Fin m → Bool) :
    Admissible (neighborhood out incoming) on f ↔ Models out on f := by
  unfold Admissible Models
  simp only [neighborhood, Finset.mem_insert, Prod.mk.injEq, and_true, Finset.mem_image,
    exists_eq_right, and_true]
  constructor
  · rintro ⟨h, h'⟩
    exact ⟨h, fun i j hi hj he => h' i j hi hj (Or.inr he)⟩
  · rintro ⟨h, h'⟩
    refine ⟨h, fun i j hi hj he => ?_⟩
    rcases he with rfl | he
    · exact id
    · exact h' i j hi hj he

theorem interval_bags {m l width : ℕ} (lo hi : Tip m → Fin l)
    (ordered : ∀ p, lo p ≤ hi p)
    (out incoming : Fin m → Finset (Fin m)) (tr : ∀ i j, j ∈ out i ↔ i ∈ incoming j)
    (small : ∀ t : Fin l, (Finset.univ.filter (fun p => lo p ≤ t ∧ t ≤ hi p)).card ≤ width)
    (marked : ∀ i, lo (i,false) ≤ hi (i,true) ∧ lo (i,true) ≤ hi (i,false))
    (arc : ∀ i j, j ∈ out i → lo (i,true) ≤ hi (j,false) ∧ lo (j,false) ≤ hi (i,true)) :
    ∃ bag : Fin l → Finset (Tip m), (∀ t, (bag t).card ≤ width) ∧
      (∀ p, ∃ t, p ∈ bag t) ∧
      (∀ p r, r ∈ neighborhood out incoming p → ∃ t, p ∈ bag t ∧ r ∈ bag t) ∧
      ∀ p s t u, s ≤ t → t ≤ u → p ∈ bag s → p ∈ bag u → p ∈ bag t := by
  classical
  let bag := fun t : Fin l => Finset.univ.filter (fun p => lo p ≤ t ∧ t ≤ hi p)
  have member (p : Tip m) (t : Fin l) : p ∈ bag t ↔ lo p ≤ t ∧ t ≤ hi p := by simp [bag]
  have meet (p r : Tip m) (hpr : lo p ≤ hi r) (hrp : lo r ≤ hi p) :
      ∃ t, p ∈ bag t ∧ r ∈ bag t := by
    refine ⟨max (lo p) (lo r), (member ..).2 ⟨le_max_left .., max_le (ordered _) hrp⟩,
      (member ..).2 ⟨le_max_right .., max_le hpr (ordered _)⟩⟩
  refine ⟨bag, small, fun p => ⟨lo p, (member ..).2 ⟨le_rfl, ordered p⟩⟩, ?_, ?_⟩
  · rintro ⟨i,b⟩ ⟨j,c⟩ hr
    cases b <;> cases c <;> simp [neighborhood] at hr
    · rcases hr with rfl | he
      · exact meet _ _ (marked _).1 (marked _).2
      · have h := arc j i ((tr j i).2 he)
        exact meet _ _ h.2 h.1
    · rcases hr with rfl | he
      · exact meet _ _ (marked _).2 (marked _).1
      · have h := arc i j he
        exact meet _ _ h.1 h.2
  · intro p s t u hst htu hps hpu
    exact (member ..).2 ⟨((member ..).1 hps).1.trans hst, htu.trans ((member ..).1 hpu).2⟩


set_option maxHeartbeats 2000000 in
theorem of_implication_host
    (H : letI : ∀ p : Prop, Decidable p := Classical.propDecidable
      ∀ n k q : Nat, 2 ≤ q →
        let L := Nat.log2 q + 1
        ∃ (m : Nat) (out incoming : Fin m → Finset (Fin m))
          (source : Fin m → Option ((Fin k × Fin n × Bool) ⊕ (Fin k × Fin L)))
          (l : Nat) (lo hi : Tip m → Fin l),
          m ≤ 81000*(n+1)*(k+1)*(L+1)^2 ∧
          (∀ i j, j ∈ out i ↔ i ∈ incoming j) ∧ (∀ i, (out i).card ≤ 2) ∧
          (∀ i, (incoming i).card ≤ 2) ∧ l ≤ 4*m+1 ∧ (∀ p, lo p ≤ hi p) ∧
          (∀ t : Fin l, (Finset.univ.filter (fun p => lo p ≤ t ∧ t ≤ hi p)).card ≤ n+45) ∧
          (∀ i, lo (i,false) ≤ hi (i,true) ∧ lo (i,true) ≤ hi (i,false)) ∧
          (∀ i j, j ∈ out i → lo (i,true) ≤ hi (j,false) ∧ lo (j,false) ≤ hi (i,true)) ∧
          ∀ (lit : Fin k → Fin n → Bool → Bool) (weight : Fin k → Fin q),
            let code := fun e => ((weight e).val + q - 1) % q
            let active := fun i => (source i).elim true (Sum.elim
              (fun p => lit p.1 p.2.1 p.2.2)
              (fun p => !((code p.1).testBit p.2.val)))
            let factor := fun (y : Fin n → Bool) (e : Fin k) =>
              if ∀ i, lit e i (y i) = false then (weight e).val else 1
            (Finset.univ.filter (Models out active)).card % q =
              (∑ y : Fin n → Bool, ∏ e : Fin k, factor y e) % q) : (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ n k q : Nat, 2 ≤ q →
  let L := Nat.log2 q + 1
  ∃ (m : Nat) (nb : (Fin m × Bool) → Finset (Fin m × Bool))
    (source : Fin m → Option ((Fin k × Fin n × Bool) ⊕ (Fin k × Fin L))),
    m ≤ 81000*(n+1)*(k+1)*(L+1)^2 ∧
    (∀ p, p ∉ nb p ∧ (nb p).card ≤ 3) ∧
    (∀ p r, r ∈ nb p ↔ p ∈ nb r) ∧ (∀ p, ∀ r ∈ nb p, p.2 ≠ r.2) ∧
    (∀ i, (i,true) ∈ nb (i,false)) ∧
    (∃ (l : Nat) (bag : Fin l → Finset (Fin m × Bool)),
      l ≤ 4*m+1 ∧ (∀ t, (bag t).card ≤ n+45) ∧ (∀ p, ∃ t, p ∈ bag t) ∧
      (∀ p r, r ∈ nb p → ∃ t, p ∈ bag t ∧ r ∈ bag t) ∧
      ∀ p s t u, s ≤ t → t ≤ u → p ∈ bag s → p ∈ bag u → p ∈ bag t) ∧
    ∀ (lit : Fin k → Fin n → Bool → Bool) (weight : Fin k → Fin q),
      let code := fun e => ((weight e).val + q - 1) % q
      let active := fun i => (source i).elim true (Sum.elim
        (fun p => lit p.1 p.2.1 p.2.2)
        (fun p => !((code p.1).testBit p.2.val)))
      let live := (Finset.univ : Finset (Fin m × Bool)).filter (fun p => active p.1)
      let cover := fun (C : Finset (Fin m × Bool)) => C ⊆ live ∧
        ∀ p ∈ live, ∀ r ∈ nb p, r ∈ live → p ∈ C ∨ r ∈ C
      let opt := (Finset.univ : Finset (Finset (Fin m × Bool))).filter
        (fun C => cover C ∧ ∀ W, cover W → C.card ≤ W.card)
      let factor := fun (y : Fin n → Bool) (e : Fin k) =>
        if ∀ i, lit e i (y i) = false then (weight e).val else 1
      opt.Nonempty ∧ (∀ C ∈ opt, C.card =
        ((Finset.univ : Finset (Fin m)).filter (fun i => active i)).card) ∧
      opt.card % q = (∑ y : Fin n → Bool, ∏ e : Fin k, factor y e) % q) := by
  classical
  intro n k q hq
  obtain ⟨m,out,inc,src,l,lo,hi,hm,tr,ho,hin,hl,hord,hsize,hmatch,harc,hcount⟩ := H n k q hq
  obtain ⟨hd,hs,hb,hmk⟩ := neighborhood_properties out inc tr ho hin
  obtain ⟨bag,hbag,hv,he,hinterval⟩ := interval_bags (width := n+45) lo hi hord out inc tr
    (fun t => by convert! hsize t using 2
                 ext p
                 simp only [Finset.mem_filter]) hmatch harc
  refine ⟨m,neighborhood out inc,src,hm,hd,hs,hb,hmk,⟨l,bag,hl,hbag,hv,he,hinterval⟩,?_⟩
  intro lit weight
  let code := fun e => ((weight e).val + q - 1) % q
  let on := fun i => (src i).elim true (Sum.elim (fun p => lit p.1 p.2.1 p.2.2)
      (fun p => !((code p.1).testBit p.2.val)))
  let nb := neighborhood out inc
  change (minima nb on).Nonempty ∧ (∀ C ∈ minima nb on, C.card = (livePairs on).card) ∧ _
  obtain ⟨hne,hmin⟩ := cover_optimum (on := on) hb hmk
  refine ⟨hne,hmin,?_⟩
  change (minima nb on).card % q = _
  have hmodels : (Finset.univ.filter (Admissible nb on)) = Finset.univ.filter (Models out on) :=
    Finset.filter_congr (fun f _ => admissible_neighborhood out inc on f)
  rw [count_minima hs hb hmk,hmodels]
  convert! hcount lit weight using 3
  ext f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

end Parent

namespace Parent


def digitCount (v : ℕ) : ℕ → ℕ
  | 0 => 2
  | l + 1 => 2 * digitCount (v / 2) l + 3 + (if v.testBit 0 then 0 else 1)

theorem digitCount_spec (l v : ℕ) (hv : v < 2^l) :
    digitCount v l + v + 4 = 6 * 2^l := by
  induction l generalizing v with
  | zero =>
    have : v = 0 := by simpa using hv
    simp [this, digitCount]
  | succ l ih =>
    have hpow := Nat.two_pow_pos l
    rw [pow_succ] at hv ⊢
    have hhalf : v / 2 < 2^l := by omega
    have h := ih _ hhalf
    rw [digitCount]
    simp only [Nat.testBit_zero]
    split <;> rename_i hbit <;> simp only [decide_eq_true_eq] at hbit <;> omega

def weightedCount (q l v : ℕ) :=
  digitCount v l * (2*q - 1) + 2 + (q + (6*(2^l - 1)) % q)

theorem weightedCount_spec {q l v : ℕ} (hq : 2 ≤ q) (hv : v < 2^l) :
    (weightedCount q l v : ZMod q) = v := by
  have hD := digitCount_spec l v hv
  have hcast := congrArg (fun t : ℕ => (t : ZMod q)) hD
  push_cast at hcast
  have h1 : 1 ≤ 2*q := by omega
  have h2 : 1 ≤ 2^l := Nat.two_pow_pos l
  simp only [weightedCount, Nat.cast_add, Nat.cast_mul, Nat.cast_sub h1, Nat.cast_sub h2,
    Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, ZMod.natCast_mod, ZMod.natCast_self] at *
  linear_combination -hcast

def transfer (q : ℕ) : Bool → Bool → ℕ
  | false, true => q
  | true, false => 0
  | _, _ => 1

theorem transfer_spec (q : ℕ) (x y : Bool) :
    (transfer q x y : ZMod q) = if x = y then 1 else 0 := by
  cases x <;> cases y <;> simp [transfer]

theorem transfer_sum (q : ℕ) (x : Bool) (F : Bool → ZMod q) :
    (∑ y, (transfer q x y : ZMod q) * F y) = F x := by
  simp [transfer_spec]

def literalPass (lit : Bool → Bool) (x a b : Bool) : Bool :=
  (!(lit false) || !a || x) && (!(lit true) || !x || b)

@[simp] theorem literalPass_off (lit : Bool → Bool) (x : Bool) :
    literalPass lit x false true = true := by simp [literalPass]

@[simp] theorem literalPass_on (lit : Bool → Bool) (x : Bool) :
    literalPass lit x true false = !(lit x) := by cases x <;> simp [literalPass]

def selectors (q : ℕ) (a b : Bool) : ℕ :=
  (if a && b then q else 1) * (if !a && !b then q else 1)

theorem selectors_spec (q : ℕ) (a b : Bool) :
    (selectors q a b : ZMod q) = if a = b then 0 else 1 := by
  cases a <;> cases b <;> simp [selectors]

open Classical in
theorem clause_sum {n q : ℕ} (hq : 2 ≤ q) (lit : Fin n → Bool → Bool)
    (w : Fin q) (y : Fin n → Bool) (D : ℕ)
    (hD : (D : ZMod q) = (((w.val + q - 1) % q : ℕ) : ZMod q)) :
    (∑ a : Bool, ∑ b : Bool, (selectors q a b : ZMod q) *
      (if a then (D : ZMod q) else 1) *
      (if ∀ i, literalPass (lit i) (y i) a b = true then 1 else 0)) =
      if ∀ i, lit i (y i) = false then (w.val : ZMod q) else 1 := by
  have hw : 1 ≤ w.val + q := by omega
  rw [ZMod.natCast_mod, Nat.cast_sub hw, Nat.cast_add, ZMod.natCast_self] at hD
  simp only [Fintype.sum_bool, selectors_spec, 
    zero_mul, one_mul, Bool.false_eq_true, Bool.true_eq, literalPass_off, literalPass_on,
    Bool.not_eq_true', ↓reduceIte]
  split <;> simp_all


structure Network (X : Type) where
  V : Type
  ft : Fintype V
  source : V → Option X
  edge : V → V → Prop

instance Network.vertexFintype {X : Type} (A : Network X) : Fintype A.V := A.ft

namespace Network

variable {X : Type}
abbrev on (A : Network X) (e : X → Bool) (i : A.V) := (A.source i).elim true e
def Valid (A : Network X) (e : X → Bool) (f : A.V → Bool) : Prop :=
  (∀ i, A.on e i = false → f i = false) ∧
    ∀ i j, A.edge i j → A.on e i = true → A.on e j = true → f i = true → f j = true
abbrev State (A : Network X) (e : X → Bool) := {f : A.V → Bool // A.Valid e f}
noncomputable instance stateFintype (A : Network X) (e : X → Bool) : Fintype (A.State e) := by
  classical
  exact Fintype.ofFinite _
def zero (A : Network X) (e : X → Bool) : A.State e :=
  ⟨fun _ => false, by simp [Valid]⟩
def one (A : Network X) (e : X → Bool) : A.State e :=
  ⟨A.on e, ⟨fun _ h => h, fun _ _ _ _ h _ => h⟩⟩

def join (A B : Network X) (link : A.V → B.V → Prop) : Network X where
  V := A.V ⊕ B.V
  ft := inferInstance
  source := Sum.elim A.source B.source
  edge
    | .inl i, .inl j => A.edge i j
    | .inl i, .inr j => link i j
    | .inr _, .inl _ => False
    | .inr i, .inr j => B.edge i j

def compatible (A B : Network X) (e : X → Bool) (link : A.V → B.V → Prop)
    (f : A.V → Bool) (g : B.V → Bool) :=
  ∀ i j, link i j → A.on e i = true → B.on e j = true → f i = true → g j = true

theorem valid_join (A B : Network X) (e : X → Bool) (link : A.V → B.V → Prop)
    (f : (A.V ⊕ B.V) → Bool) :
    (join A B link).Valid e f ↔ A.Valid e (fun i => f (.inl i)) ∧
      B.Valid e (fun i => f (.inr i)) ∧
      compatible A B e link (fun i => f (.inl i)) (fun i => f (.inr i)) := by
  simp only [Valid, compatible, Sum.forall, join, on, Sum.elim_inl, Sum.elim_inr,
    false_implies, implies_true, forall_and]
  tauto

def joinEquiv (A B : Network X) (e : X → Bool) (link : A.V → B.V → Prop) :
    (join A B link).State e ≃ {p : A.State e × B.State e // compatible A B e link p.1.1 p.2.1} where
  toFun f :=
    let h := (valid_join A B e link f.1).1 f.2
    ⟨(⟨_,h.1⟩,⟨_,h.2.1⟩),h.2.2⟩
  invFun p := ⟨Sum.elim p.1.1.1 p.1.2.1,
    (valid_join ..).2 ⟨p.1.1.2,p.1.2.2,p.2⟩⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    cases i <;> rfl
  right_inv _ := rfl

end Network

structure Fragment (X : Type) extends Network X where
  input : V → Prop
  output : V → Prop
  input_live : ∃ v, input v ∧ source v = none
  output_live : ∃ v, output v ∧ source v = none
  zero_of_outputs : ∀ e (f : toNetwork.State e),
    (∀ v, output v → f.1 v = false) → f = toNetwork.zero e
  one_of_inputs : ∀ e (f : toNetwork.State e),
    (∀ v, input v → toNetwork.on e v = true → f.1 v = true) → f = toNetwork.one e

namespace Fragment

variable {X : Type}
open Network

def bridge (A B : Fragment X) (i : A.V) (j : B.V) := A.output i ∧ B.input j

theorem compatible_bridge (A B : Fragment X) (e : X → Bool)
    (f : A.toNetwork.State e) (g : B.toNetwork.State e) :
    compatible A.toNetwork B.toNetwork e (bridge A B) f.1 g.1 ↔
      f = A.toNetwork.zero e ∨ g = B.toNetwork.one e := by
  constructor
  · intro h
    by_cases hz : ∀ i, A.output i → f.1 i = false
    · exact Or.inl (A.zero_of_outputs e f hz)
    · push Not at hz
      obtain ⟨i, hi, hfi⟩ := hz
      have hi' : A.toNetwork.on e i = true := by
        cases ha : A.toNetwork.on e i
        · exact (hfi (f.2.1 i ha)).elim
        · rfl
      apply Or.inr (B.one_of_inputs e g ?_)
      exact fun j hj hj' => h i j ⟨hi,hj⟩ hi' hj' (by simpa using hfi)
  · rintro (rfl | rfl) i j _ _ hj hf
    · contradiction
    · exact hj

def parallel (A B : Fragment X) : Fragment X where
  toNetwork := join A.toNetwork B.toNetwork (fun _ _ => False)
  input := Sum.elim A.input B.input
  output := Sum.elim A.output B.output
  input_live := by
    obtain ⟨i, h, hi⟩ := A.input_live
    exact ⟨.inl i, h, hi⟩
  output_live := by
    obtain ⟨i, h, hi⟩ := A.output_live
    exact ⟨.inl i, h, hi⟩
  zero_of_outputs e f hz := by
    let s := (joinEquiv _ _ e _ f).1
    have ha := A.zero_of_outputs e s.1 (fun i hi => hz (.inl i) hi)
    have hb := B.zero_of_outputs e s.2 (fun i hi => hz (.inr i) hi)
    apply Subtype.ext
    funext v
    cases v with
    | inl i => exact congrFun (congrArg Subtype.val ha) i
    | inr i => exact congrFun (congrArg Subtype.val hb) i
  one_of_inputs e f hz := by
    let s := (joinEquiv _ _ e _ f).1
    have ha := A.one_of_inputs e s.1 (fun i hi hn => hz (.inl i) hi hn)
    have hb := B.one_of_inputs e s.2 (fun i hi hn => hz (.inr i) hi hn)
    apply Subtype.ext
    funext v
    cases v with
    | inl i => exact congrFun (congrArg Subtype.val ha) i
    | inr i => exact congrFun (congrArg Subtype.val hb) i

def series (A B : Fragment X) : Fragment X where
  toNetwork := join A.toNetwork B.toNetwork (bridge A B)
  input := Sum.elim A.input (fun _ => False)
  output := Sum.elim (fun _ => False) B.output
  input_live := by
    obtain ⟨i, h, hi⟩ := A.input_live
    exact ⟨.inl i, h, hi⟩
  output_live := by
    obtain ⟨i, h, hi⟩ := B.output_live
    exact ⟨.inr i, h, hi⟩
  zero_of_outputs e f hz := by
    let st := joinEquiv _ _ e _ f
    obtain ha | hb := (compatible_bridge A B e st.1.1 st.1.2).1 st.2
    · have hb := B.zero_of_outputs e st.1.2 (fun i hi => hz (.inr i) hi)
      apply Subtype.ext
      funext v
      cases v with
      | inl i => exact congrFun (congrArg Subtype.val ha) i
      | inr i => exact congrFun (congrArg Subtype.val hb) i
    · obtain ⟨i,hi,hn⟩ := B.output_live
      have hval := congrFun (congrArg Subtype.val hb) i
      change f.1 (.inr i) = (B.source i).elim true e at hval
      rw [hz (.inr i) hi, hn] at hval
      contradiction
  one_of_inputs e f ho := by
    let st := joinEquiv _ _ e _ f
    obtain ha | hb := (compatible_bridge A B e st.1.1 st.1.2).1 st.2
    · obtain ⟨i,hi,hn⟩ := A.input_live
      have hval := congrFun (congrArg Subtype.val ha) i
      change f.1 (.inl i) = false at hval
      have ht := ho (.inl i) hi (by change (A.source i).elim true e = true; rw [hn]; rfl)
      rw [ht] at hval
      contradiction
    · have ha := A.one_of_inputs e st.1.1 (fun i hi hh => ho (.inl i) hi hh)
      apply Subtype.ext
      funext v
      cases v with
      | inl i => exact congrFun (congrArg Subtype.val ha) i
      | inr i => exact congrFun (congrArg Subtype.val hb) i

noncomputable def num (A : Fragment X) (e : X → Bool) := Fintype.card (A.toNetwork.State e)

theorem num_parallel (A B : Fragment X) (e : X → Bool) :
    (parallel A B).num e = A.num e * B.num e := by
  classical
  let eqv : (parallel A B).toNetwork.State e ≃ A.toNetwork.State e × B.toNetwork.State e :=
    (joinEquiv _ _ e _).trans (Equiv.subtypeUnivEquiv (fun _ _ _ h => h.elim))
  exact (Fintype.card_congr eqv).trans (Fintype.card_prod ..)

theorem num_series (A B : Fragment X) (e : X → Bool) :
    (series A B).num e + 1 = A.num e + B.num e := by
  classical
  let a := A.toNetwork.zero e
  let b := B.toNetwork.one e
  let eqv : (series A B).toNetwork.State e ≃
      {p : A.toNetwork.State e × B.toNetwork.State e // p.1 = a ∨ p.2 = b} :=
    (joinEquiv _ _ e _).trans (Equiv.subtypeEquivRight (fun p => compatible_bridge A B e p.1 p.2))
  have decomp : {p : A.toNetwork.State e × B.toNetwork.State e // p.1 = a ∨ p.2 = b} ≃
      B.toNetwork.State e ⊕ {u : A.toNetwork.State e // u ≠ a} := {
    toFun := fun ⟨(u,v),_⟩ => if h : u = a then .inl v else .inr ⟨u,h⟩
    invFun := fun s => match s with
      | .inl v => ⟨(a,v), Or.inl rfl⟩
      | .inr u => ⟨(u.1,b), Or.inr rfl⟩
    left_inv := by
      rintro ⟨⟨u,v⟩,h⟩
      dsimp at h
      by_cases hu : u = a
      · subst u; simp
      · obtain rfl := h.resolve_left hu
        simp [hu]
    right_inv := by
      rintro (v|⟨u,hu⟩) <;> simp_all }
  have hpos : Nonempty (A.toNetwork.State e) := ⟨a⟩
  have hc := Fintype.card_congr (eqv.trans decomp)
  simp [num, Fintype.card_subtype_compl] at hc ⊢
  have := Fintype.card_pos (α := A.toNetwork.State e)
  omega


def atom (X : Type) : Fragment X where
  V := Unit
  ft := inferInstance
  source := fun _ => none
  edge := fun _ _ => False
  input := fun _ => True
  output := fun _ => True
  input_live := ⟨(), trivial, rfl⟩
  output_live := ⟨(), trivial, rfl⟩
  zero_of_outputs _ _ h := Subtype.ext (funext (fun i => h i trivial))
  one_of_inputs _ _ h := Subtype.ext (funext (fun i => h i trivial rfl))

@[simp] theorem num_atom (e : X → Bool) : (atom X).num e = 2 := by
  let eqv : (atom X).toNetwork.State e ≃ Bool := {
    toFun := fun f => f.1 ()
    invFun := fun b => ⟨fun _ => b, by simp [Network.Valid, atom, Network.on]⟩
    left_inv := fun _ => Subtype.ext (funext (fun | () => rfl))
    right_inv := fun _ => rfl }
  exact (Fintype.card_congr eqv).trans Fintype.card_bool

def cap (x : X) : Fragment X where
  V := Bool
  ft := inferInstance
  source := fun b => if b then none else some x
  edge := fun i j => i = false ∧ j = true
  input := fun _ => True
  output := fun j => j = true
  input_live := ⟨true, trivial, rfl⟩
  output_live := ⟨true, rfl, rfl⟩
  zero_of_outputs e f h := by
    apply Subtype.ext
    funext b
    cases b
    · change f.1 false = false
      cases ha : e x
      · exact f.2.1 false ha
      · cases hv : f.1 false
        · rfl
        · have h' := f.2.2 false true ⟨rfl,rfl⟩ ha rfl hv
          rw [h true rfl] at h'
          contradiction
    · exact h true rfl
  one_of_inputs e f h := by
    apply Subtype.ext
    funext b
    change f.1 b = (if b then none else some x).elim true e
    cases hb : (if b then none else some x).elim true e
    · exact f.2.1 b hb
    · exact h b trivial hb

abbrev CapPair (b : Bool) := {p : Bool × Bool // p.1 = true → b = true ∧ p.2 = true}

theorem num_cap (e : X → Bool) (x : X) : (cap x).num e = 2 + (e x).toNat := by
  let eqv : (cap x).toNetwork.State e ≃ CapPair (e x) := {
    toFun := fun f => ⟨(f.1 false, f.1 true), by
      intro h
      cases he : e x
      · have hf := f.2.1 false he
        rw [hf] at h
        contradiction
      · exact ⟨rfl, f.2.2 false true ⟨rfl,rfl⟩ he rfl h⟩⟩
    invFun := fun p => ⟨fun (b : Bool) => if b then p.1.2 else p.1.1, by
      constructor
      · intro b hb
        cases b
        · change e x = false at hb
          change p.1.1 = false
          cases he : p.1.1
          · rfl
          · exact (Bool.noConfusion (hb.symm.trans (p.2 he).1))
        · contradiction
      · rintro i j ⟨rfl,rfl⟩ _ _ h
        exact (p.2 h).2⟩
    left_inv := fun _ => Subtype.ext (funext (fun | false => rfl | true => rfl))
    right_inv := fun _ => rfl }
  unfold num
  rw [Fintype.card_congr eqv]
  cases e x <;> decide

def box (A B : Fragment X) := series (series (atom X) (parallel A B)) (atom X)
def dbl (A : Fragment X) := box A (atom X)

theorem num_box (A B : Fragment X) (e : X → Bool) :
    (box A B).num e = A.num e * B.num e + 2 := by
  have h := num_series (series (atom X) (parallel A B)) (atom X) e
  have h' := num_series (atom X) (parallel A B) e
  rw [num_atom] at h
  rw [num_atom, num_parallel] at h'
  unfold box
  omega

theorem num_dbl (A : Fragment X) (e : X → Bool) : (dbl A).num e = 2 * A.num e + 2 := by
  simp [dbl, num_box, Nat.mul_comm]

def size (A : Fragment X) := Fintype.card A.V

@[simp] theorem vertices_series (A B : Fragment X) :
    (series A B).size = A.size + B.size := Fintype.card_sum
@[simp] theorem vertices_parallel (A B : Fragment X) :
    (parallel A B).size = A.size + B.size := Fintype.card_sum
@[simp] theorem vertices_atom : (atom X).size = 1 := Fintype.card_unit
@[simp] theorem vertices_cap (x : X) : (cap x).size = 2 := Fintype.card_bool
theorem vertices_box (A B : Fragment X) :
    (box A B).size = A.size + B.size + 2 := by simp [box]; omega
theorem vertices_dbl (A : Fragment X) : (dbl A).size = A.size + 3 := by
  simp [dbl, vertices_box]

def chain (X : Type) : ℕ → Fragment X
  | 0 => atom X
  | j + 1 => series (chain X j) (atom X)

theorem chain_spec (e : X → Bool) (d : ℕ) :
    (chain X d).num e = d + 2 ∧ (chain X d).size = d + 1 := by
  induction d with
  | zero => simp [chain]
  | succ d ih =>
    have h := num_series (chain X d) (atom X) e
    rw [num_atom, ih.1] at h
    simp only [chain, vertices_series, vertices_atom, ih.2]
    exact ⟨by omega,trivial⟩

def constant (X : Type) (t : ℕ) : Fragment X :=
  if 6 ≤ t then
    let A := dbl (constant X ((t-2)/2))
    if (t-2)%2 = 0 then A else series A (atom X)
  else chain X (t-2)
termination_by t
decreasing_by omega

theorem constant_spec (X : Type) (e : X → Bool) (t : ℕ) (ht : 2 ≤ t) :
    (constant X t).num e = t ∧ (constant X t).size ≤ 4*(t.log2+1) := by
  induction t using Nat.strong_induction_on with
  | ind t ih =>
    rw [constant]
    split
    · rename_i hlarge
      let u := (t-2)/2
      have hu : 2 ≤ u := by dsimp [u]; omega
      have hlt : u < t := by dsimp [u]; omega
      have hlog : u.log2 < t.log2 := by
        have hupper := @Nat.lt_log2_self t
        apply (Nat.log2_lt (by omega)).2
        dsimp [u]
        rw [pow_succ] at hupper
        omega
      obtain ⟨hnum,hcard⟩ := ih u hlt hu
      change (constant X ((t-2)/2)).num e = u at hnum
      split
      · rw [num_dbl, hnum, vertices_dbl]
        change (constant X ((t-2)/2)).size ≤ _ at hcard
        dsimp [u] at *
        omega
      · have hs := num_series (dbl (constant X u)) (atom X) e
        rw [num_atom, num_dbl, hnum] at hs
        simp only [vertices_series, vertices_atom, vertices_dbl]
        dsimp [u] at *
        omega
    · have hs := chain_spec e (t-2)
      have hp := @Nat.lt_log2_self t
      by_cases hlog : t.log2 = 0
      · simp [hlog] at hp
        omega
      · omega


def digits : (L : ℕ) → (Fin L → X) → Fragment X
  | 0, _ => atom X
  | l+1, tag => series (dbl (digits l (fun i => tag i.succ))) (cap (tag 0))

theorem digits_spec (l : ℕ) (tag : Fin l → X) (e : X → Bool) (v : ℕ)
    (he : ∀ i, e (tag i) = !(v.testBit i.val)) :
    (digits l tag).num e = digitCount v l ∧ (digits l tag).size = 1 + 5*l := by
  induction l generalizing v with
  | zero => simp [digits,digitCount]
  | succ l ih =>
    let p := digits l (fun i => tag i.succ)
    have hrec := ih (fun i => tag i.succ) (v/2) (fun i => by
      simpa [Nat.testBit_div_two] using he i.succ)
    have h := num_series (dbl p) (cap (tag 0)) e
    rw [num_dbl, num_cap, he] at h
    change p.num e = _ ∧ p.size = _ at hrec
    rw [hrec.1] at h
    change (series (dbl p) (cap (tag 0))).num e = _ ∧
      (series (dbl p) (cap (tag 0))).size = _
    rw [vertices_series, vertices_dbl, hrec.2, vertices_cap, digitCount]
    change (series (dbl p) (cap (tag 0))).num e + 1 =
      2 * digitCount (v/2) l + 2 + (2 + (!v.testBit 0).toNat) at h
    cases hb : v.testBit 0 <;> rw [hb] at h <;> simp only [Bool.not_false, Bool.not_true, Bool.toNat_true, Bool.toNat_false, Bool.false_eq_true, ite_true, ite_false] at h ⊢ <;> omega

def weightBlock (q l : ℕ) (tag : Fin l → X) : Fragment X :=
  series (box (digits l tag) (constant X (2*q-1)))
    (constant X (q+1+(6*(2^l-1))%q))

theorem weightBlock_spec (q l : ℕ) (hq : 2 ≤ q) (hl : l = q.log2 + 1)
    (tag : Fin l → X) (e : X → Bool) (v : ℕ) (hv : v < q)
    (he : ∀ i, e (tag i) = !(v.testBit i.val)) :
    ((weightBlock q l tag).num e : ZMod q) = v ∧
    (weightBlock q l tag).size ≤ 13*l + 15 := by
  let t := q+1+(6*(2^l-1))%q
  have ht : 2 ≤ t := by dsimp [t]; omega
  have hm : (6*(2^l-1))%q < q := Nat.mod_lt _ (by omega)
  have ht' : t ≤ 2*q := by dsimp [t]; omega
  have hc := constant_spec X e (2*q-1) (by omega)
  have hct := constant_spec X e t ht
  have hd := digits_spec l tag e v he
  have hsum := num_series (box (digits l tag) (constant X (2*q-1))) (constant X t) e
  rw [num_box, hc.1, hct.1, hd.1] at hsum
  have hv' : v < 2^l := by
    rw [hl]
    exact hv.trans (@Nat.lt_log2_self q)
  refine ⟨?_,?_⟩
  · convert weightedCount_spec hq hv' using 2
    unfold weightBlock weightedCount
    dsimp [t] at hsum
    omega
  · have log_bound (u : ℕ) (hu : 2 ≤ u) (hu' : u ≤ 2*q) : u.log2 ≤ l := by
      have h := @Nat.lt_log2_self q
      rw [← hl] at h
      have hh : u < 2^(l+1) := by rw [pow_succ]; omega
      have := (Nat.log2_lt (by omega : u ≠ 0)).2 hh
      omega
    have h1 := log_bound (2*q-1) (by omega) (by omega)
    have h2 := log_bound t ht ht'
    change (series (box (digits l tag) (constant X (2*q-1))) (constant X t)).size ≤ _
    rw [vertices_series, vertices_box, hd.2]
    omega

open Classical in
noncomputable def pins (A : Fragment X) (e : X → Bool) (a b : Bool) :=
  (Finset.univ : Finset (A.toNetwork.State e)).filter (fun f =>
    (a = true → ∀ i, A.input i → A.toNetwork.on e i = true → f.1 i = true) ∧
    (b = false → ∀ i, A.output i → f.1 i = false))

theorem mem_pins (A : Fragment X) (e : X → Bool) (a b : Bool) (f : A.State e) :
    f ∈ A.pins e a b ↔
      (a = true → ∀ i, A.input i → A.on e i = true → f.1 i = true) ∧
      (b = false → ∀ i, A.output i → f.1 i = false) := by simp [pins]

theorem pin_card (A : Fragment X) (e : X → Bool) (a b : Bool) :
    (A.pins e a b).card = transfer (A.num e) a b := by
  classical
  have h (f : A.toNetwork.State e) : f ∈ A.pins e a b ↔
      (a = true → f = A.toNetwork.one e) ∧ (b = false → f = A.toNetwork.zero e) := by
    simp only [pins, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1,h2⟩
      exact ⟨fun ha => A.one_of_inputs e _ (h1 ha), fun hb => A.zero_of_outputs e _ (h2 hb)⟩
    · rintro ⟨h1,h2⟩
      constructor
      · intro ha i _ hi
        rw [h1 ha]
        exact hi
      · intro hb i _
        rw [h2 hb]
        rfl
  have hd : A.toNetwork.one e ≠ A.toNetwork.zero e := by
    obtain ⟨i,_,hi⟩ := A.input_live
    intro hh
    have he := congrFun (congrArg Subtype.val hh) i
    simp [Network.one, Network.zero, Network.on,hi] at he
  cases a <;> cases b
  · have he : A.pins e false false = {A.toNetwork.zero e} := by ext f; simp [h]
    simp [he,transfer]
  · have he : A.pins e false true = Finset.univ := by ext f; simp [h]
    simp [he,transfer,num]
  · have he : A.pins e true false = ∅ := by
      ext f
      simp only [h, true_implies, Finset.notMem_empty, iff_false, not_and]
      rintro rfl
      exact hd
    simp [he,transfer]
  · have he : A.pins e true true = {A.toNetwork.one e} := by ext f; simp [h]
    simp [he,transfer]

end Fragment
structure Component (X K : Type) extends Network X where
  incoming : K → V → Prop
  outgoing : V → K → Prop

namespace Component
variable {X K J : Type} [Fintype K] [Fintype J]

def Fits (B : Component X K) (e : X → Bool) (c : K → Bool) (f : B.State e) : Prop :=
  (∀ u v, B.incoming u v → B.on e v = true → c u = true → f.1 v = true) ∧
  (∀ v u, B.outgoing v u → B.on e v = true → f.1 v = true → c u = true)

def Fiber (B : Component X K) (e : X → Bool) (c : K → Bool) := {f : B.State e // B.Fits e c f}
noncomputable instance (B : Component X K) (e : X → Bool) (c : K → Bool) : Fintype (B.Fiber e c) := by
  classical
  unfold Fiber
  infer_instance

inductive Edge (B : J → Component X K) : (K ⊕ (Σ j, (B j).V)) → (K ⊕ (Σ j, (B j).V)) → Prop
  | inner (j u v) : (B j).edge u v → Edge B (.inr ⟨j,u⟩) (.inr ⟨j,v⟩)
  | enter (j u v) : (B j).incoming u v → Edge B (.inl u) (.inr ⟨j,v⟩)
  | leave (j v u) : (B j).outgoing v u → Edge B (.inr ⟨j,v⟩) (.inl u)

def assembled (B : J → Component X K) : Network X where
  V := K ⊕ (Σ j, (B j).V)
  ft := inferInstance
  source := Sum.elim (fun _ => none) (fun v => (B v.1).source v.2)
  edge := Edge B

def decomposition (B : J → Component X K) (e : X → Bool) :
    (assembled B).State e ≃ Σ c : K → Bool, ∀ j, (B j).Fiber e c where
  toFun f := ⟨fun u => f.1 (.inl u), fun j =>
    ⟨⟨fun v => f.1 (.inr ⟨j,v⟩), ⟨fun v hv => f.2.1 _ hv,
      fun u v he => f.2.2 _ _ (.inner j u v he)⟩⟩,
      ⟨fun u v h hv hu => f.2.2 _ _ (.enter j u v h) rfl hv hu,
       fun v u h hv hf => f.2.2 _ _ (.leave j v u h) hv rfl hf⟩⟩⟩
  invFun p := ⟨Sum.elim p.1 (fun v => (p.2 v.1).1.1 v.2), by
    constructor
    · rintro (u|⟨j,v⟩) h
      · contradiction
      · exact (p.2 j).1.2.1 v h
    · intro u v he hu hv hf
      cases he with
      | inner j i l h => exact (p.2 j).1.2.2 i l h hu hv hf
      | enter j i l h => exact (p.2 j).2.1 i l h hv hf
      | leave j l i h => exact (p.2 j).2.2 l i h hu hf⟩
  left_inv f := by
    apply Subtype.ext
    funext v
    rcases v with u | ⟨j,v⟩ <;> rfl
  right_inv _ := rfl

theorem count_assembled [DecidableEq K] (B : J → Component X K) (e : X → Bool) :
    Fintype.card ((assembled B).State e) = ∑ c : K → Bool, ∏ j, Fintype.card ((B j).Fiber e c) := by
  classical
  rw [Fintype.card_congr (decomposition B e), Fintype.card_sigma]
  simp only [Fintype.card_pi]

def block (A : Fragment X) (before after : List K) : Component X K where
  toNetwork := A.toNetwork
  incoming u v := u ∈ before ∧ A.input v
  outgoing v u := A.output v ∧ u ∈ after

omit [Fintype K] in
theorem block_count (A : Fragment X) (before after : List K) (e : X → Bool) (c : K → Bool) :
    Fintype.card ((block A before after).Fiber e c) =
      transfer (A.num e) (before.any c) (after.all c) := by
  classical
  let eqv : (block A before after).Fiber e c ≃ ↥(A.pins e (before.any c) (after.all c)) :=
    Equiv.subtypeEquivRight (fun f => by
      change ((∀ u v, (u ∈ before ∧ A.input v) → A.on e v = true → c u = true → f.1 v = true) ∧
        (∀ v u, (A.output v ∧ u ∈ after) → A.on e v = true → f.1 v = true → c u = true)) ↔ f ∈ A.pins e (before.any c) (after.all c)
      refine Iff.trans ?_ (Fragment.mem_pins A e (before.any c) (after.all c) f).symm
      simp only [List.any_eq_true]
      constructor
      · rintro ⟨hp,hs⟩
        constructor
        · rintro ⟨u,hu,hh⟩ v hv hc
          exact hp u v ⟨hu,hv⟩ hc hh
        · intro ha v hv
          cases hf : f.1 v
          · rfl
          · have hon : A.on e v = true := by
              cases hh : A.on e v
              · exact (f.2.1 v hh).symm.trans hf
              · rfl
            have hall : after.all c = true :=
              List.all_eq_true.mpr (fun u hu => hs v u ⟨hv,hu⟩ hon hf)
            rw [hall] at ha
            contradiction
      · rintro ⟨hp,hs⟩
        constructor
        · rintro u v ⟨hu,hv⟩ h ha
          exact hp ⟨u,hu,ha⟩ v hv h
        · rintro v u ⟨hv,hu⟩ _ hh
          cases ha : after.all c
          · exact Bool.noConfusion ((hs ha v hv).symm.trans hh)
          · exact List.all_eq_true.mp ha u hu)
  exact (Fintype.card_congr eqv).trans ((Fintype.card_coe _).trans (Fragment.pin_card ..))

def switch (x : X) (before after : List K) : Component X K where
  V := Unit
  ft := inferInstance
  source := fun _ => some x
  edge := fun _ _ => False
  incoming u _ := u ∈ before
  outgoing _ u := u ∈ after

abbrev SwitchBit (on lo hi : Bool) := {b : Bool //
  (on = false → b = false) ∧ (on = true → lo = true → b = true) ∧
  (on = true → b = true → hi = true)}

omit [Fintype K] in
theorem switch_count (x : X) (before after : List K) (e : X → Bool) (c : K → Bool) :
    Fintype.card ((switch x before after).Fiber e c) =
      if e x then transfer 2 (before.any c) (after.all c) else 1 := by
  let eqv : (switch x before after).Fiber e c ≃ SwitchBit (e x) (before.any c) (after.all c) := {
    toFun := fun f => ⟨f.1.1 (), f.1.2.1 (), by
      rintro ha h
      obtain ⟨u,hu,hc⟩ := List.any_eq_true.mp h
      exact f.2.1 u () hu ha hc, fun ha hb => List.all_eq_true.mpr (fun u hu => f.2.2 () u hu ha hb)⟩
    invFun := fun b => ⟨⟨fun _ => b.1, ⟨fun _ => b.2.1, fun _ _ h => h.elim⟩⟩,
      ⟨fun u _ hu he hc => b.2.2.1 he (List.any_eq_true.mpr ⟨u,hu,hc⟩),
       fun _ u hu he hf => List.all_eq_true.mp (b.2.2.2 he hf) u hu⟩⟩
    left_inv := fun _ => Subtype.ext (Subtype.ext (funext (fun | () => rfl)))
    right_inv := fun _ => rfl }
  rw [Fintype.card_congr eqv]
  cases e x <;> cases before.any c <;> cases after.all c <;> decide

end Component
namespace Construction

abbrev Core (n k : ℕ) := (Fin n × Fin (k+1)) ⊕ (Fin k × Bool × Fin (n+1))
abbrev Tag (n k l : ℕ) := (Fin k × Fin n × Bool) ⊕ (Fin k × Fin l)
abbrev Group (n : ℕ) := Fin 3 ⊕ (Fin n × Fin 5)
abbrev Index (n k : ℕ) := Fin k × Group n
abbrev var {n k} (i : Fin n) (t : Fin (k+1)) : Core n k := .inl (i,t)
abbrev sel {n k} (e : Fin k) (s : Bool) (t : Fin (n+1)) : Core n k := .inr (e,s,t)

def part (n k q l : ℕ) (s : Index n k) : Component (Tag n k l) (Core n k) :=
  let e := s.1
  let fixed := Fragment.constant (Tag n k l) q
  match s.2 with
  | .inl j =>
    let a := sel e false 0
    let b := sel e true 0
    match j.val with
    | 0 => Component.block fixed [] [a,b]
    | 1 => Component.block fixed [a,b] []
    | _ => Component.block (Fragment.weightBlock q l (fun z => Sum.inr (e,z))) [] [a]
  | .inr (i,j) =>
    let a := sel e false i.succ
    let b := sel e true i.succ
    let x := var i e.succ
    match j.val with
    | 0 => Component.block fixed [var i e.castSucc] [x]
    | 1 => Component.block fixed [sel e false i.castSucc] [a]
    | 2 => Component.block fixed [sel e true i.castSucc] [b]
    | 3 => Component.switch (.inl (e,i,false)) [a] [a,x]
    | _ => Component.switch (.inl (e,i,true)) [b,x] [b]

def env {n k q l} (lit : Fin k → Fin n → Bool → Bool) (weight : Fin k → Fin q) :
    Tag n k l → Bool :=
  Sum.elim (fun p => lit p.1 p.2.1 p.2.2)
    (fun p => !(((weight p.1).val + q - 1) % q).testBit p.2.val)

def Consistent {n k} (c : Core n k → Bool) : Prop :=
  (∀ (i : Fin n) (e : Fin k), c (var i e.castSucc) = c (var i e.succ)) ∧
  (∀ (e : Fin k) (s : Bool) (i : Fin n), c (sel e s i.castSucc) = c (sel e s i.succ))

abbrev Data (n k : ℕ) := (Fin n → Bool) × (Fin k → Bool × Bool)

def expand {n k} (d : Data n k) : Core n k → Bool
  | .inl (i,_) => d.1 i
  | .inr (e,false,_) => (d.2 e).1
  | .inr (e,true,_) => (d.2 e).2

theorem expand_consistent {n k} (d : Data n k) : Consistent (expand d) := by
  refine ⟨fun _ _ => rfl, ?_⟩
  intro e s i
  cases s <;> rfl

theorem fin_const {d} (f : Fin (d+1) → Bool)
    (h : ∀ i : Fin d, f i.castSucc = f i.succ) (j : Fin (d+1)) : f 0 = f j :=
  Fin.induction rfl (fun i ih => ih.trans (h i)) j

def compressed {n k} : Data n k ≃ {c : Core n k → Bool // Consistent c} where
  toFun d := ⟨expand d, expand_consistent d⟩
  invFun c := (fun i => c.1 (var i 0), fun e => (c.1 (sel e false 0),c.1 (sel e true 0)))
  left_inv _ := rfl
  right_inv c := by
    apply Subtype.ext
    funext v
    rcases v with ⟨i,t⟩ | ⟨e,s,t⟩
    · exact fin_const (fun t => c.1 (var i t)) (c.2.1 i) t
    · cases s <;> exact fin_const (fun t => c.1 (sel e _ t)) (c.2.2 e _) t

noncomputable def term {n k q l} (H : Tag n k l → Bool) (c : Core n k → Bool)
    (s : Index n k) : ZMod q := Fintype.card ((part n k q l s).Fiber H c)

theorem move_var {n k q l} (hq : 2 ≤ q) (H : Tag n k l → Bool) (c : Core n k → Bool)
    (i : Fin n) (e : Fin k) :
    term (q:=q) H c (e,.inr (i,0)) =
      if c (var i e.castSucc) = c (var i e.succ) then 1 else 0 := by
  simp [term, part, Component.block_count, (Fragment.constant_spec _ H q hq).1, transfer_spec]

theorem move_a {n k q l} (hq : 2 ≤ q) (H : Tag n k l → Bool) (c : Core n k → Bool)
    (i : Fin n) (e : Fin k) :
    term (q:=q) H c (e,.inr (i,1)) =
      if c (sel e false i.castSucc) = c (sel e false i.succ) then 1 else 0 := by
  simp [term, part, Component.block_count, (Fragment.constant_spec _ H q hq).1, transfer_spec]

theorem move_b {n k q l} (hq : 2 ≤ q) (H : Tag n k l → Bool) (c : Core n k → Bool)
    (i : Fin n) (e : Fin k) :
    term (q:=q) H c (e,.inr (i,2)) =
      if c (sel e true i.castSucc) = c (sel e true i.succ) then 1 else 0 := by
  simp [term, part, Component.block_count, (Fragment.constant_spec _ H q hq).1, transfer_spec]

theorem vanish {n k q l} (hq : 2 ≤ q) (H : Tag n k l → Bool) (c : Core n k → Bool)
    (hc : ¬Consistent c) : (∏ s, term (q:=q) H c s) = 0 := by
  classical
  by_cases hv : ∀ (i : Fin n) (e : Fin k), c (var i e.castSucc) = c (var i e.succ)
  · have hh : ¬ ∀ (e : Fin k) (s : Bool) (i : Fin n), c (sel e s i.castSucc) = c (sel e s i.succ) :=
      fun h => hc ⟨hv,h⟩
    push Not at hh
    obtain ⟨e,s,i,hs⟩ := hh
    cases s
    · exact Finset.prod_eq_zero (Finset.mem_univ (e,Sum.inr (i,1))) (by rw [move_a hq, ite_eq_right hs])
    · exact Finset.prod_eq_zero (Finset.mem_univ (e,Sum.inr (i,2))) (by rw [move_b hq, ite_eq_right hs])
  · push Not at hv
    obtain ⟨i,e,h⟩ := hv
    exact Finset.prod_eq_zero (Finset.mem_univ (e,Sum.inr (i,0))) (by rw [move_var hq, ite_eq_right h])

theorem switch_pair (lf lt x a b : Bool) :
    (if lf then transfer 2 a (a && x) else 1) *
      (if lt then transfer 2 (b || x) b else 1) =
      if literalPass (fun z => if z then lt else lf) x a b then 1 else 0 := by
  cases lf <;> cases lt <;> cases x <;> cases a <;> cases b <;> rfl

theorem occurrences {n k q l} (hq : 2 ≤ q) (H : Tag n k l → Bool) (d : Data n k)
    (e : Fin k) (i : Fin n) :
    (∏ j : Fin 5, term (q:=q) H (expand d) (e,.inr (i,j))) =
    if literalPass (fun z => H (.inl (e,i,z))) (d.1 i) (d.2 e).1 (d.2 e).2 then 1 else 0 := by
  rw [Fin.prod_univ_five]
  rw [move_var hq, move_a hq, move_b hq]
  simp only [expand, ite_true, one_mul]
  have he (z : Bool) : H (.inl (e,i,z)) = if z then H (.inl (e,i,true)) else H (.inl (e,i,false)) :=
    by cases z <;> rfl
  have h := switch_pair (H (.inl (e,i,false))) (H (.inl (e,i,true))) (d.1 i) (d.2 e).1 (d.2 e).2
  convert congrArg (fun x : ℕ => (x : ZMod q)) h using 1
  · simp [term,part,Component.switch_count,expand, Nat.cast_ite]
  · rw [show (fun z => H (.inl (e,i,z))) = _ from funext he]
    simp [Nat.cast_ite]

noncomputable abbrev weightNum {n k q l} (H : Tag n k l → Bool) (e : Fin k) :=
  (Fragment.weightBlock q l (fun z => (Sum.inr (e,z) : Tag n k l))).num H

theorem roots {n k q l} (hq : 2 ≤ q) (H : Tag n k l → Bool) (d : Data n k) (e : Fin k) :
    (∏ j : Fin 3, term (q:=q) H (expand d) (e,.inl j)) =
      (selectors q (d.2 e).1 (d.2 e).2 : ZMod q) *
        (if (d.2 e).1 then (weightNum (q:=q) H e : ZMod q) else 1) := by
  rw [Fin.prod_univ_three]
  cases ha : (d.2 e).1 <;> cases hb : (d.2 e).2 <;>
    simp [term, part, Component.block_count, (Fragment.constant_spec _ H q hq).1,
      expand, ha, hb, selectors, transfer, weightNum]

open Classical in
noncomputable def score {n k q l} (H : Tag n k l → Bool) (y : Fin n → Bool) (e : Fin k)
    (a b : Bool) : ZMod q :=
  (selectors q a b : ZMod q) * (if a then (weightNum (q:=q) H e : ZMod q) else 1) *
    (if ∀ i, literalPass (fun z => H (.inl (e,i,z))) (y i) a b = true then 1 else 0)

theorem product_consistent {n k q l} (hq : 2 ≤ q) (H : Tag n k l → Bool) (d : Data n k) :
    (∏ s, term (q:=q) H (expand d) s) = ∏ e, score H d.1 e (d.2 e).1 (d.2 e).2 := by
  classical
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro e _
  rw [Fintype.prod_sum_type, Fintype.prod_prod_type, roots hq]
  simp_rw [occurrences hq]
  unfold score
  congr 1
  by_cases hh : ∀ i, literalPass (fun z => H (.inl (e,i,z))) (d.1 i) (d.2 e).1 (d.2 e).2 = true
  · simp [hh]
  · rw [ite_eq_right hh]
    push Not at hh
    obtain ⟨i,hi⟩ := hh
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem sum_consistent {n k q l} (hq : 2 ≤ q) (H : Tag n k l → Bool) :
    (∑ c : Core n k → Bool, ∏ s, term (q:=q) H c s) =
      ∑ d : Data n k, ∏ e, score H d.1 e (d.2 e).1 (d.2 e).2 := by
  classical
  let F := fun c => ∏ s, term (q:=q) H c s
  change ∑ c, F c = _
  calc
    _ = ∑ c : {c : Core n k → Bool // Consistent c}, F c.1 := by
      rw [← Finset.sum_subtype (Finset.univ.filter Consistent) (fun c => by simp) F]
      apply Eq.symm
      exact Finset.sum_subset (Finset.filter_subset ..)
        (fun c _ hc => vanish hq H c (by simpa using hc))
    _ = ∑ d : Data n k, F (expand d) := by
      exact (Equiv.sum_comp compressed (fun c => F c.1)).symm
    _ = _ := Finset.sum_congr rfl (fun d _ => product_consistent hq H d)

open Classical in
theorem host_count (n k q : ℕ) (hq : 2 ≤ q) (lit : Fin k → Fin n → Bool → Bool)
    (w : Fin k → Fin q) :
    let l := q.log2+1
    let H := env (l:=l) lit w
    Fintype.card ((Component.assembled (part n k q l)).State H) % q =
      (∑ y : Fin n → Bool, ∏ e : Fin k,
        if ∀ i, lit e i (y i) = false then (w e).val else 1) % q := by
  classical
  let l := q.log2+1
  let H := env (l:=l) lit w
  change Fintype.card ((Component.assembled (part n k q l)).State H) % q = _
  apply (ZMod.natCast_eq_natCast_iff' _ _ _).1
  rw [Component.count_assembled]
  push_cast
  change (∑ c : Core n k → Bool, ∏ s, term (q:=q) H c s) = _
  rw [sum_consistent hq, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y _
  rw [← Fintype.prod_sum (fun (e : Fin k) (p : Bool × Bool) => score (q:=q) H y e p.1 p.2)]
  apply Finset.prod_congr rfl
  intro e _
  rw [Fintype.sum_prod_type]
  let v := ((w e).val + q - 1) % q
  have hv : v < q := Nat.mod_lt _ (by omega)
  have hw := (Fragment.weightBlock_spec q l hq rfl
    (fun z => (Sum.inr (e,z) : Tag n k l)) H v hv (fun _ => rfl)).1
  exact clause_sum hq (lit e) (w e) y _ hw


theorem host_size (n k q : ℕ) (hq : 2 ≤ q) :
    let l := q.log2+1
    Fintype.card (Component.assembled (part n k q l)).V ≤ 81000*(n+1)*(k+1)*(l+1)^2 := by
  let l := q.log2+1
  let B := part n k q l
  let N := 13*l + 15
  have hconst := (Fragment.constant_spec (Tag n k l) (fun _ => false) q hq).2
  have hb (s : Index n k) : Fintype.card (B s).V ≤ N := by
    rcases s with ⟨e,j | ⟨i,j⟩⟩
    · fin_cases j
      · change (Fragment.constant _ q).size ≤ N
        dsimp [N,l] at *
        omega
      · change (Fragment.constant _ q).size ≤ N
        dsimp [N,l] at *
        omega
      · change (Fragment.weightBlock q l (fun z => (Sum.inr (e,z) : Tag n k l))).size ≤ N
        exact (Fragment.weightBlock_spec q l hq rfl _ (fun _ => true) 0 (by omega)
          (by simp)).2
    · fin_cases j
      all_goals first | (change (Fragment.constant _ q).size ≤ N; dsimp [N,l] at *; omega)
                      | (change Fintype.card Unit ≤ N; simp [N])
  change Fintype.card (Core n k ⊕ (Σ j, (B j).V)) ≤ _
  rw [Fintype.card_sum,Fintype.card_sigma]
  have hs : ∑ j, Fintype.card (B j).V ≤ Fintype.card (Index n k) * N :=
    (Finset.sum_le_sum (fun j _ => hb j)).trans_eq (by simp)
  simp [Core,Index,Group] at hs ⊢
  dsimp [N,l] at *
  nlinarith only [hs, Nat.zero_le n, Nat.zero_le k, Nat.zero_le q.log2,
    Nat.zero_le (n*k), Nat.zero_le (n*q.log2), Nat.zero_le (k*q.log2),
    Nat.zero_le (n*k*q.log2), Nat.zero_le (q.log2^2), Nat.zero_le (n*q.log2^2),
    Nat.zero_le (k*q.log2^2), Nat.zero_le (n*k*q.log2^2)]

end Construction

def Bounded {V : Type} (P : V → Prop) (n : ℕ) : Prop :=
  ∃ s : List V, s.length ≤ n ∧ ∀ v, P v → v ∈ s

namespace Bounded
variable {V W : Type} {P : V → Prop} {Q : W → Prop} {n m : ℕ}
theorem weaken {P' : V → Prop} (h : Bounded P n) (hp : ∀ v, P' v → P v) (hn : n ≤ m) :
    Bounded P' m := by
  obtain ⟨s,hs,h⟩ := h
  exact ⟨s,hs.trans hn,fun v hv => h v (hp v hv)⟩

theorem none : Bounded (fun _ : V => False) 0 := ⟨[], le_rfl, fun _ h => h.elim⟩
theorem single (v : V) : Bounded (fun u => u = v) 1 :=
  ⟨[v],le_rfl,fun _ h => by simp [h]⟩

theorem split (hp : Bounded P n) (hq : Bounded Q m) : Bounded (Sum.elim P Q) (n+m) := by
  obtain ⟨s,hs,h⟩ := hp
  obtain ⟨t,ht,h'⟩ := hq
  refine ⟨s.map Sum.inl ++ t.map Sum.inr, by simp; omega, ?_⟩
  rintro (v|w) hv
  · exact List.mem_append_left _ (List.mem_map_of_mem (h _ hv))
  · exact List.mem_append_right _ (List.mem_map_of_mem (h' _ hv))

theorem left (hp : Bounded P n) : Bounded (Sum.elim P (fun _ : W => False)) n := by
  simpa using hp.split (none (V:=W))
theorem right (hq : Bounded Q m) : Bounded (Sum.elim (fun _ : V => False) Q) m := by
  simpa using (none (V:=V)).split hq

theorem map {U} (g : V → U) (hp : Bounded P n) :
    Bounded (fun x => ∃ y, P y ∧ g y = x) n := by
  obtain ⟨s,hs,h⟩ := hp
  refine ⟨s.map g, by simpa using hs, ?_⟩
  rintro _ ⟨y,hy,rfl⟩
  exact List.mem_map_of_mem (h _ hy)

theorem union {Q : V → Prop} (hp : Bounded P n) (hq : Bounded Q m) : Bounded (fun v => P v ∨ Q v) (n+m) := by
  obtain ⟨s,hs,h⟩ := hp
  obtain ⟨t,ht,h'⟩ := hq
  exact ⟨s++t, by simp; omega, fun v hv => List.mem_append.mpr (hv.imp (h v) (h' v))⟩

theorem bool (P : Bool → Prop) : Bounded P 2 :=
  ⟨[false,true], le_rfl, fun v _ => by cases v <;> simp⟩
theorem unit (P : Unit → Prop) : Bounded P 1 :=
  ⟨[()], le_rfl, fun _ _ => by simp⟩

end Bounded

namespace Fragment
variable {X : Type}

structure Ports (A : Fragment X) (bi bo ri ro : ℕ) : Prop where
  ins : Bounded A.input bi
  outs : Bounded A.output bo
  ind : ∀ u, Bounded (A.edge · u) 2
  outd : ∀ u, Bounded (A.edge u) 2
  freeIn : ∀ u, A.input u → Bounded (A.edge · u) (2-ri)
  freeOut : ∀ u, A.output u → Bounded (A.edge u) (2-ro)

private theorem parallel_neighbors {A B : Type} (P : A → A → Prop) (Q : B → B → Prop)
    (E : A ⊕ B → A ⊕ B → Prop)
    (hll : ∀ i j, E (.inl i) (.inl j) ↔ P i j) (hrr : ∀ i j, E (.inr i) (.inr j) ↔ Q i j)
    (hlr : ∀ i j, ¬E (.inl i) (.inr j)) (hrl : ∀ i j, ¬E (.inr i) (.inl j))
    (n : ℕ) (IA : A → Prop) (IB : B → Prop)
    (hA : ∀ i, IA i → Bounded (P i) n) (hB : ∀ i, IB i → Bounded (Q i) n) :
    ∀ i, Sum.elim IA IB i → Bounded (E i) n := by
  rintro (i|j) hi
  · exact (hA i hi).left.weaken (fun | .inl u,h => (hll ..).1 h | .inr u,h => hlr i u h) le_rfl
  · exact (hB j hi).right.weaken (fun | .inl u,h => hrl j u h | .inr u,h => (hrr ..).1 h) le_rfl

theorem ports_parallel {A B : Fragment X} {ai ao bi bo ri ro : ℕ}
    (ha : A.Ports ai ao ri ro) (hb : B.Ports bi bo ri ro) :
    (parallel A B).Ports (ai+bi) (ao+bo) ri ro := by
  refine ⟨ha.ins.split hb.ins, ha.outs.split hb.outs, ?_, ?_, ?_, ?_⟩
  · exact fun i => parallel_neighbors (fun i j => A.edge j i) (fun i j => B.edge j i)
      (fun i j => (parallel A B).edge j i) (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl)
      (fun _ _ => id) (fun _ _ => id) 2 (fun _ => True) (fun _ => True)
      (fun i _ => ha.ind i) (fun i _ => hb.ind i) i (by cases i <;> trivial)
  · exact fun i => parallel_neighbors A.edge B.edge (parallel A B).edge (fun _ _ => Iff.rfl)
      (fun _ _ => Iff.rfl) (fun _ _ => id) (fun _ _ => id) 2 (fun _ => True) (fun _ => True)
      (fun i _ => ha.outd i) (fun i _ => hb.outd i) i (by cases i <;> trivial)
  · exact parallel_neighbors (fun i j => A.edge j i) (fun i j => B.edge j i)
      (fun i j => (parallel A B).edge j i) (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl)
      (fun _ _ => id) (fun _ _ => id) _ _ _ ha.freeIn hb.freeIn
  · exact parallel_neighbors A.edge B.edge (parallel A B).edge (fun _ _ => Iff.rfl)
      (fun _ _ => Iff.rfl) (fun _ _ => id) (fun _ _ => id) _ _ _ ha.freeOut hb.freeOut

theorem ports_series {A B : Fragment X} {ai ao bi bo ari aro bri bro : ℕ}
    (ha : A.Ports ai ao ari aro) (hb : B.Ports bi bo bri bro)
    (h1 : ao + (2-bri) ≤ 2) (h2 : (2-aro) + bi ≤ 2) :
    (series A B).Ports ai bo ari bro := by
  classical
  refine ⟨ha.ins.left,hb.outs.right,?_,?_,?_,?_⟩
  · rintro (u|v)
    · exact (ha.ind u).left.weaken (fun | .inl _,h => h | .inr _,h => h) le_rfl
    · by_cases h : B.input v
      · exact (ha.outs.split (hb.freeIn v h)).weaken
          (fun | .inl _,he => he.1 | .inr _, he => he) h1
      · exact (hb.ind v).right.weaken (fun | .inl _,he => h he.2 | .inr _,he => he) le_rfl
  · rintro (u|v)
    · by_cases h : A.output u
      · exact ((ha.freeOut u h).split hb.ins).weaken
          (fun | .inl _,he => he | .inr _,he => he.2) h2
      · exact (ha.outd u).left.weaken (fun | .inl _,he => he | .inr _,he => h he.1) le_rfl
    · exact (hb.outd v).right.weaken (fun | .inl _,h => h | .inr _,h => h) le_rfl
  · rintro (u|v) h
    · exact (ha.freeIn u h).left.weaken (fun | .inl _,h => h | .inr _,h => h) le_rfl
    · exact h.elim
  · rintro (u|v) h
    · exact h.elim
    · exact (hb.freeOut v h).right.weaken (fun | .inl _,h => h | .inr _,h => h) le_rfl

abbrev Regular (A : Fragment X) := A.Ports 1 1 2 2

theorem ports_atom : (atom X).Regular :=
  ⟨Bounded.unit _,Bounded.unit _,fun _ => ⟨[], by simp,fun _ h => h.elim⟩,
    fun _ => ⟨[],by simp,fun _ h => h.elim⟩,fun _ _ => Bounded.none,fun _ _ => Bounded.none⟩

theorem ports_cap (x : X) : (cap x).Ports 2 1 1 2 :=
  ⟨Bounded.bool _,Bounded.single true,fun _ => Bounded.bool _,fun _ => Bounded.bool _,
    fun _ _ => (Bounded.single false).weaken (fun _ h => h.1) le_rfl,
    fun _ h => ⟨[],by simp, fun _ he => Bool.noConfusion (h.symm.trans he.1)⟩⟩

theorem ports_box {A B : Fragment X} (ha : A.Regular) (hb : B.Regular) : (box A B).Regular :=
  ports_series (ports_series ports_atom (ports_parallel ha hb) (by decide) (by decide))
    ports_atom (by decide) (by decide)

theorem ports_dbl {A : Fragment X} (h : A.Regular) : (dbl A).Regular := ports_box h ports_atom

theorem ports_chain (d : ℕ) : (chain X d).Regular := by
  induction d with
  | zero => exact ports_atom
  | succ d ih => exact ports_series ih ports_atom (by decide) (by decide)

theorem ports_constant (t : ℕ) : (constant X t).Regular := by
  induction t using Nat.strong_induction_on with
  | ind t ih =>
    rw [constant]
    split
    · have hh := ports_dbl (ih ((t-2)/2) (by omega))
      split
      · exact hh
      · exact ports_series hh ports_atom (by decide) (by decide)
    · exact ports_chain _

theorem ports_digits (l : ℕ) (tag : Fin l → X) : (digits l tag).Regular := by
  induction l with
  | zero => exact ports_atom
  | succ l ih => exact ports_series (ports_dbl (ih _)) (ports_cap _) (by decide) (by decide)

theorem ports_weight (q l : ℕ) (tag : Fin l → X) : (weightBlock q l tag).Regular :=
  ports_series (ports_box (ports_digits ..) (ports_constant _)) (ports_constant _) (by decide) (by decide)

end Fragment


namespace Bounded

theorem fiber {J : Type} {V : J → Type} {P : J → Prop} {Q : (j : J) → V j → Prop}
    {n : ℕ} (hj : Bounded P n) (hv : ∀ j, Bounded (Q j) 1) :
    Bounded (fun v : Sigma V => P v.1 ∧ Q v.1 v.2) n := by
  classical
  obtain ⟨s,hs,hm⟩ := hj
  choose t ht hmem using hv
  let f (j : J) := (t j).map (Sigma.mk j)
  have hlen (z : List J) : (z.flatMap f).length ≤ z.length := by
    induction z with
    | nil => exact le_rfl
    | cons j z ih =>
      have := ht j
      simp [f,List.flatMap_cons] at *
      omega
  refine ⟨s.flatMap f,(hlen _).trans hs,?_⟩
  rintro ⟨j,v⟩ ⟨hj,hv⟩
  exact List.mem_flatMap.mpr ⟨j,hm j hj,List.mem_map_of_mem (hmem j v hv)⟩

end Bounded

namespace Component
variable {X K J : Type} [Fintype K] [Fintype J]

structure Safe (B : Component X K) : Prop where
  ind : ∀ v, Bounded (Sum.elim (B.incoming · v) (B.edge · v)) 2
  outd : ∀ v, Bounded (Sum.elim (B.outgoing v) (B.edge v)) 2
  inputs : ∀ u, Bounded (B.incoming u) 1
  outputs : ∀ u, Bounded (B.outgoing · u) 1

omit [Fintype K] in
theorem safe_block {A : Fragment X} (ha : A.Regular) (p r : List K)
    (hp : p.length ≤ 2) (hr : r.length ≤ 2) : (block A p r).Safe := by
  classical
  refine ⟨?_,?_,?_,?_⟩
  · intro v
    by_cases hv : A.input v
    · have h : Bounded (fun x => x ∈ p) 2 := ⟨p,hp,fun _ hx => hx⟩
      exact (h.split (ha.freeIn v hv)).weaken
        (fun | .inl _,h => h.1 | .inr _,h => h) le_rfl
    · exact (ha.ind v).right.weaken
        (fun | .inl _,h => hv h.2 | .inr _,h => h) le_rfl
  · intro v
    by_cases hv : A.output v
    · have h : Bounded (fun x => x ∈ r) 2 := ⟨r,hr,fun _ hx => hx⟩
      exact (h.split (ha.freeOut v hv)).weaken
        (fun | .inl _,h => h.2 | .inr _,h => h) le_rfl
    · exact (ha.outd v).right.weaken
        (fun | .inl _,h => hv h.1 | .inr _,h => h) le_rfl
  · exact fun _ => ha.ins.weaken (fun _ h => h.2) le_rfl
  · exact fun _ => ha.outs.weaken (fun _ h => h.1) le_rfl

omit [Fintype K] in
theorem safe_switch (x : X) (p r : List K) (hp : p.length ≤ 2) (hr : r.length ≤ 2) :
    (switch x p r).Safe := by
  have h : Bounded (fun x => x ∈ p) 2 := ⟨p,hp,fun _ hx => hx⟩
  have h' : Bounded (fun x => x ∈ r) 2 := ⟨r,hr,fun _ hx => hx⟩
  exact ⟨fun _ => h.left,fun _ => h'.left,fun _ => Bounded.unit _,fun _ => Bounded.unit _⟩

def embed (B : J → Component X K) (j : J) : (K ⊕ (B j).V) → (assembled B).V :=
  Sum.elim Sum.inl (fun v => Sum.inr ⟨j,v⟩)

theorem safe_assembled (B : J → Component X K) (hb : ∀ j, (B j).Safe)
    (hi : ∀ u, Bounded (fun j => ∃ v, (B j).incoming u v) 2)
    (ho : ∀ u, Bounded (fun j => ∃ v, (B j).outgoing v u) 2) (v : (assembled B).V) :
    Bounded ((assembled B).edge · v) 2 ∧ Bounded ((assembled B).edge v) 2 := by
  rcases v with u | ⟨j,v⟩
  · have Hi := (ho u).fiber (fun j => (hb j).outputs u)
    have Ho := (hi u).fiber (fun j => (hb j).inputs u)
    constructor
    · apply Hi.right.weaken _ le_rfl
      intro v he
      cases he with
      | leave j v u h => exact ⟨⟨v,h⟩,h⟩
    · apply Ho.right.weaken _ le_rfl
      intro v he
      cases he with
      | enter j u v h => exact ⟨⟨v,h⟩,h⟩
  · constructor
    · apply ((hb j).ind v |>.map (embed B j)).weaken _ le_rfl
      intro x he
      cases he with
      | inner j u v h => exact ⟨.inr u,h,rfl⟩
      | enter j u v h => exact ⟨.inl u,h,rfl⟩
    · apply ((hb j).outd v |>.map (embed B j)).weaken _ le_rfl
      intro x he
      cases he with
      | inner j u v h => exact ⟨.inr v,h,rfl⟩
      | leave j v u h => exact ⟨.inl u,h,rfl⟩

end Component

namespace Construction

theorem part_safe (n k q l : ℕ) (s : Index n k) : (part n k q l s).Safe := by
  rcases s with ⟨e,j | ⟨i,j⟩⟩
  · fin_cases j
    all_goals first
      | exact Component.safe_block (Fragment.ports_constant _) _ _ (by simp) (by simp)
      | exact Component.safe_block (Fragment.ports_weight ..) _ _ (by simp) (by simp)
  · fin_cases j
    all_goals first
      | exact Component.safe_block (Fragment.ports_constant _) _ _ (by simp) (by simp)
      | exact Component.safe_switch _ _ _ (by simp) (by simp)

def before {n k} (s : Index n k) : List (Core n k) :=
  let e := s.1
  match s.2 with
  | .inl j => if j.val = 1 then [sel e false 0, sel e true 0] else []
  | .inr (i,j) =>
    match j.val with
    | 0 => [var i e.castSucc]
    | 1 => [sel e false i.castSucc]
    | 2 => [sel e true i.castSucc]
    | 3 => [sel e false i.succ]
    | _ => [sel e true i.succ, var i e.succ]

def after {n k} (s : Index n k) : List (Core n k) :=
  let e := s.1
  match s.2 with
  | .inl j => match j.val with
    | 0 => [sel e false 0,sel e true 0]
    | 1 => []
    | _ => [sel e false 0]
  | .inr (i,j) =>
    match j.val with
    | 0 => [var i e.succ]
    | 1 => [sel e false i.succ]
    | 2 => [sel e true i.succ]
    | 3 => [sel e false i.succ, var i e.succ]
    | _ => [sel e true i.succ]

theorem endpoints {n k q l} (s : Index n k) (u : Core n k) (v : (part n k q l s).V) :
    ((part n k q l s).incoming u v → u ∈ before s) ∧ ((part n k q l s).outgoing v u → u ∈ after s) := by
  rcases s with ⟨e,j | ⟨i,j⟩⟩
  · fin_cases j <;> exact ⟨And.left,And.right⟩
  · fin_cases j
    all_goals first | exact ⟨And.left,And.right⟩ | exact ⟨id,id⟩

end Construction
end Parent

namespace Parent
namespace Construction
def prev {d} {α : Type} (t : Fin (d+1)) (z : List α) (f : Fin d → List α) : List α :=
  Fin.cases z f t
def next {d} {α : Type} (t : Fin (d+1)) (f : Fin d → List α) : List α :=
  Fin.lastCases [] f t

@[simp] theorem prev_succ {d α} (t : Fin d) (z : List α) (f : Fin d → List α) :
    prev t.succ z f = f t := by simp [prev]
@[simp] theorem prev_zero {d α} (z : List α) (f : Fin d → List α) : prev 0 z f = z := rfl
@[simp] theorem next_cast {d α} (t : Fin d) (f : Fin d → List α) : next t.castSucc f = f t := by simp [next]

theorem len_prev {d α} (t : Fin (d+1)) {z : List α} {f : Fin d → List α} {m}
    (hz : z.length ≤ m) (hf : ∀ i, (f i).length ≤ m) : (prev t z f).length ≤ m :=
  Fin.cases hz (fun i => by simpa using hf i) t
theorem len_next {d α} (t : Fin (d+1)) {f : Fin d → List α} {m}
    (hf : ∀ i, (f i).length ≤ m) : (next t f).length ≤ m :=
  Fin.lastCases (by simp [next]) (fun i => by simpa using hf i) t

def srcSlots {n k} : Core n k → List (Index n k)
  | .inl (i,t) => next t (fun e => [(e,.inr (i,0))]) ++ prev t [] (fun e => [(e,.inr (i,4))])
  | .inr (e,b,t) => next t (fun i => [(e,.inr (i,if b then 2 else 1))]) ++
      prev t [(e,.inl 1)] (fun i => [(e,.inr (i,if b then 4 else 3))])

def dstSlots {n k} : Core n k → List (Index n k)
  | .inl (i,t) => prev t [] (fun e => [(e,.inr (i,0)),(e,.inr (i,3))])
  | .inr (e,b,t) => prev t (if b then [(e,.inl 0)] else [(e,.inl 0),(e,.inl 2)])
      (fun i => [(e,.inr (i,if b then 2 else 1)),(e,.inr (i,if b then 4 else 3))])

theorem slots_len {n k} (u : Core n k) : (srcSlots u).length ≤ 2 ∧ (dstSlots u).length ≤ 2 := by
  rcases u with ⟨i,t⟩ | ⟨e,b,t⟩
  · constructor
    · exact List.length_append .. ▸ Nat.add_le_add (len_next _ (m:=1) (by simp)) (len_prev _ (m:=1) (by simp) (by simp))
    · exact len_prev _ (by simp) (by simp)
  · cases b <;> constructor
    all_goals first
      | exact List.length_append .. ▸ Nat.add_le_add (len_next _ (m:=1) (by simp)) (len_prev _ (m:=1) (by simp) (by simp))
      | exact len_prev _ (by simp) (by simp)

theorem slots_cover {n k} (s : Index n k) (u : Core n k) :
    (u ∈ before s → s ∈ srcSlots u) ∧ (u ∈ after s → s ∈ dstSlots u) := by
  rcases s with ⟨e,j | ⟨i,j⟩⟩
  · fin_cases j <;> constructor <;> simp [before,after] <;>
      intro h <;> rcases h with (rfl|rfl) | rfl <;> simp [srcSlots,dstSlots]
  · fin_cases j <;> constructor <;> simp [before,after] <;>
      intro h <;> rcases h with (rfl|rfl) | rfl <;> simp [srcSlots,dstSlots]

theorem host_degree (n k q l : ℕ) (v : (Component.assembled (part n k q l)).V) :
    Bounded ((Component.assembled (part n k q l)).edge · v) 2 ∧
    Bounded ((Component.assembled (part n k q l)).edge v) 2 := by
  apply Component.safe_assembled _ (part_safe n k q l)
  · intro u
    refine ⟨srcSlots u,(slots_len u).1,?_⟩
    rintro j ⟨v,h⟩
    exact (slots_cover j u).1 ((endpoints j u v).1 h)
  · intro u
    refine ⟨dstSlots u,(slots_len u).2,?_⟩
    rintro j ⟨v,h⟩
    exact (slots_cover j u).2 ((endpoints j u v).2 h)

end Construction
end Parent

namespace Parent
structure Span where
  lo : ℕ
  hi : ℕ
  ord : lo ≤ hi

namespace Span
def contains (s : Span) (t : ℕ) := s.lo ≤ t ∧ t ≤ s.hi
def meets (s r : Span) := s.lo ≤ r.hi ∧ r.lo ≤ s.hi
theorem sym {s r : Span} (h : s.meets r) : r.meets s := h.symm
def shift (s : Span) (d : ℕ) : Span := ⟨d+s.lo,d+s.hi,Nat.add_le_add_left s.ord _⟩
end Span

structure Layout (V : Type) (edge : V → V → Prop) (port : V → Prop) (w : ℕ) where
  stop : ℕ
  atV : V → Span
  limit : ∀ v, (atV v).hi ≤ stop
  pin : ∀ v, port v → (atV v).hi = stop
  meet : ∀ i j, edge i j → (atV i).meets (atV j)
  small : ∀ t, Bounded (fun v => (atV v).contains t) w

namespace Layout
variable {U V Z : Type} {E : U → U → Prop} {P : U → Prop} {w : ℕ}
def all (E : U → U → Prop) (P : U → Prop) (h : Bounded (fun _ : U => True) w) :
    Layout U E P w where
  stop := 0
  atV := fun _ => ⟨0,0,le_rfl⟩
  limit _ := le_rfl
  pin _ _ := rfl
  meet _ _ _ := ⟨le_rfl, le_rfl⟩
  small _ := h.weaken (fun _ _ => trivial) le_rfl

def ofMap (a : Layout U E P w) (f : V ≃ U) (F : V → V → Prop) (Q : V → Prop)
    (he : ∀ i j, F i j → E (f i) (f j)) (hp : ∀ i, Q i → P (f i)) :
    Layout V F Q w where
  stop := a.stop
  atV v := a.atV (f v)
  limit v := a.limit (f v)
  pin v h := a.pin _ (hp v h)
  meet i j h := a.meet _ _ (he i j h)
  small t := ((a.small t).map f.symm).weaken (fun v hv => ⟨f v,hv,f.symm_apply_apply v⟩) le_rfl

inductive Across (E : U → U → Prop) (F : V → V → Prop) (P : U → Prop) (Q : V → Prop) :
    U ⊕ V → U ⊕ V → Prop
  | left (i j) : E i j → Across E F P Q (.inl i) (.inl j)
  | right (i j) : F i j → Across E F P Q (.inr i) (.inr j)
  | lr (i j) : P i → Q j → Across E F P Q (.inl i) (.inr j)
  | rl (i j) : Q i → P j → Across E F P Q (.inr i) (.inl j)

noncomputable def append {F : V → V → Prop} {Q : V → Prop} {b c d}
    (a : Layout U E P w) (z : Layout V F Q b) (hp : Bounded P c)
    (ha : w ≤ d) (hz : c+b ≤ d) :
    Layout (U ⊕ V) (Across E F P Q) (Sum.elim P Q) d := by
  classical
  let off := a.stop+1
  let finish := off+z.stop
  have hle (i : U) : (a.atV i).hi ≤ finish := by have := a.limit i; dsimp [finish,off]; omega
  let lift (i : U) : Span := ⟨(a.atV i).lo, if P i then finish else (a.atV i).hi,
    by split <;> first | exact (a.atV i).ord.trans (hle _) | exact (a.atV i).ord⟩
  let s : U ⊕ V → Span := Sum.elim lift (fun v => (z.atV v).shift off)
  have hhi (i : U) : (a.atV i).hi ≤ (lift i).hi := by
    dsimp [lift]; split <;> first | exact hle _ | exact le_rfl
  have cross (i : U) (j : V) (hi : P i) (hj : Q j) : (lift i).meets ((z.atV j).shift off) := by
    have := (a.atV i).ord.trans (a.limit i)
    have := (z.atV j).ord.trans (z.limit j)
    simp [Span.meets,lift,hi,Span.shift,finish,off]
    omega
  refine ⟨finish,s,?_,?_,?_,?_⟩
  · rintro (i|j)
    · change (if P i then finish else _) ≤ finish
      split <;> first | exact le_rfl | exact hle _
    · exact Nat.add_le_add_left (z.limit _) _
  · rintro (i|j) h
    · exact ite_eq_left h
    · exact congrArg (off+·) (z.pin _ h)
  · intro i j h
    cases h with
    | left i j h =>
      exact ⟨(a.meet i j h).1.trans (hhi j),(a.meet i j h).2.trans (hhi i)⟩
    | right i j h =>
      exact ⟨Nat.add_le_add_left (z.meet i j h).1 _, Nat.add_le_add_left (z.meet i j h).2 _⟩
    | lr i j hi hj => exact cross i j hi hj
    | rl i j hi hj => exact (cross j i hj hi).symm
  · intro t
    by_cases ht : t < off
    · apply (a.small t).left.weaken _ ha
      rintro (i|j) h
      · change (lift i).contains t at h
        change (a.atV i).lo ≤ t ∧ t ≤ (a.atV i).hi
        refine ⟨h.1,?_⟩
        by_cases hi : P i
        · rw [a.pin i hi]; dsimp [off] at ht; omega
        · simpa [lift,hi] using h.2
      · have hh : off+(z.atV j).lo ≤ t := h.1
        omega
    · apply (hp.split (z.small (t-off))).weaken _ hz
      rintro (i|j) h
      · change P i
        by_contra hn
        have hh : t ≤ (lift i).hi := h.2
        simp [lift,hn] at hh
        have := a.limit i
        dsimp [off] at ht
        omega
      · have hh : off+(z.atV j).lo ≤ t ∧ t ≤ off+(z.atV j).hi := h
        change (z.atV j).lo ≤ t-off ∧ t-off ≤ (z.atV j).hi
        omega
end Layout

namespace Fragment
variable {X : Type}
abbrev Port (A : Fragment X) (v : A.V) := A.input v ∨ A.output v
abbrev Draw (A : Fragment X) (w : ℕ) := Layout A.V A.edge A.Port w
theorem port_bound {A : Fragment X} {a b c d} (h : A.Ports a b c d) :
    Bounded A.Port (a+b) := h.ins.union h.outs

noncomputable def drawParallel {A B : Fragment X} {a b c d}
    (x : A.Draw a) (y : B.Draw b) (hp : Bounded A.Port c)
    (ha : a ≤ d) (hb : c+b ≤ d) : (parallel A B).Draw d :=
  (x.append y hp ha hb).ofMap (Equiv.refl _) _ _
    (fun | .inl i,.inl j,h => .left i j h | .inr i,.inr j,h => .right i j h
         | .inl _,.inr _,h => h.elim | .inr _,.inl _,h => h.elim)
    (fun | .inl _,h => h | .inr _,h => h)

noncomputable def drawSeries {A B : Fragment X} {a b c d}
    (x : A.Draw a) (y : B.Draw b) (hp : Bounded A.Port c)
    (ha : a ≤ d) (hb : c+b ≤ d) : (series A B).Draw d :=
  (x.append y hp ha hb).ofMap (Equiv.refl _) _ _
    (fun | .inl i,.inl j,h => .left i j h | .inr i,.inr j,h => .right i j h
         | .inl i,.inr j,h => .lr i j (.inr h.1) (.inl h.2) | .inr _,.inl _,h => h.elim)
    (fun | .inl _,h => .inl (h.elim id False.elim) | .inr _,h => .inr (h.elim False.elim id))

noncomputable def drawSeriesRev {A B : Fragment X} {a b c d}
    (x : A.Draw a) (y : B.Draw b) (hp : Bounded B.Port c)
    (hb : b ≤ d) (ha : c+a ≤ d) : (series A B).Draw d :=
  (y.append x hp hb ha).ofMap (Equiv.sumComm _ _) _ _
    (fun | .inl i,.inl j,h => .right i j h | .inr i,.inr j,h => .left i j h
         | .inl i,.inr j,h => .rl i j (.inr h.1) (.inl h.2) | .inr _,.inl _,h => h.elim)
    (fun | .inl _,h => .inl (h.elim id False.elim) | .inr _,h => .inr (h.elim False.elim id))

def drawAtom : (atom X).Draw 1 := Layout.all _ _ (Bounded.unit _)
def drawCap (x : X) : (cap x).Draw 2 := Layout.all _ _ (Bounded.bool _)

noncomputable def drawBox {A B : Fragment X} {a b d}
    (x : A.Draw a) (y : B.Draw b) (h : A.Regular) (k : B.Regular)
    (ha : a ≤ d) (hb : 2+b ≤ d) (hd : 5 ≤ d) : (box A B).Draw d := by
  let p := drawParallel x y (port_bound h) ha hb
  let hp := ports_parallel h k
  let u := drawSeriesRev drawAtom p (port_bound hp) le_rfl hd
  exact drawSeries u drawAtom (port_bound (ports_series ports_atom hp (by decide) (by decide))) le_rfl (by omega)

noncomputable def drawDbl {A : Fragment X} (x : A.Draw 5) (h : A.Regular) : (dbl A).Draw 5 :=
  drawBox x drawAtom h ports_atom le_rfl (by decide) le_rfl

noncomputable def drawChain (d : ℕ) : (chain X d).Draw 5 := by
  induction d with
  | zero => exact Layout.all _ _ ((Bounded.unit _).weaken (fun _ _ => trivial) (by decide))
  | succ d ih => exact drawSeries ih drawAtom (port_bound (ports_chain d)) le_rfl (by decide)

theorem drawConst (t : ℕ) : Nonempty ((constant X t).Draw 5) := by
  induction t using Nat.strong_induction_on with
  | ind t ih =>
    rw [constant]
    split
    · obtain ⟨x⟩ := ih ((t-2)/2) (by omega)
      let u := drawDbl x (ports_constant _)
      split
      · exact ⟨u⟩
      · exact ⟨drawSeries u drawAtom (port_bound (ports_dbl (ports_constant _))) le_rfl (by decide)⟩
    · exact ⟨drawChain _⟩

noncomputable def drawDigits (l : ℕ) (tag : Fin l → X) : (digits l tag).Draw 5 := by
  induction l with
  | zero => exact Layout.all _ _ ((Bounded.unit _).weaken (fun _ _ => trivial) (by decide))
  | succ l ih => exact drawSeries (drawDbl (ih _) (ports_digits ..)) (drawCap _)
                    (port_bound (ports_dbl (ports_digits ..))) le_rfl (by decide)

noncomputable def drawWeight (q l : ℕ) (tag : Fin l → X) : (weightBlock q l tag).Draw 7 := by
  let u := drawBox (drawDigits l tag) (drawConst (2*q-1)).some (ports_digits ..) (ports_constant _)
    (d:=7) (by decide) (by decide) (by decide)
  exact drawSeries u (drawConst _).some (port_bound (ports_box (ports_digits ..) (ports_constant _))) le_rfl (by decide)
end Fragment
end Parent

namespace Parent

namespace Bounded
variable {V : Type} [Fintype V] {P : V → Prop} {n : ℕ}
theorem card [DecidablePred P] (h : Bounded P n) :
    (Finset.univ.filter P).card ≤ n := by
  classical
  obtain ⟨l,hl,hm⟩ := h
  exact (Finset.card_le_card (show Finset.univ.filter P ⊆ l.toFinset from
    fun i hi => List.mem_toFinset.mpr (hm i (Finset.mem_filter.mp hi).2))).trans
    (l.toFinset_card_le.trans hl)

theorem byInj {W : Type} [Fintype W] (f : V → W)
    (hf : ∀ i, P i → ∀ j, P j → f i = f j → i = j) (hn : Fintype.card W ≤ n) : Bounded P n := by
  classical
  let s := Finset.univ.filter P
  have hc := Fintype.card_le_of_injective (fun i : s => f i.1) (by
    intro i j h
    exact Subtype.ext (hf _ (Finset.mem_filter.mp i.2).2 _ (Finset.mem_filter.mp j.2).2 h))
  refine ⟨s.toList,?_,fun i hi => Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)⟩
  simpa using hc.trans hn
end Bounded

namespace Construction
def stamp {n} (row : ℕ) (col : Fin (n+1)) := row*(n+1)+col.val

theorem stamp_lt {n a b} (i j : Fin (n+1)) (h : a < b) : stamp a i < stamp b j := by
  have hh := Nat.mul_le_mul_right (n+1) (show a+1 ≤ b from h)
  simp only [Nat.add_mul,Nat.one_mul] at hh
  dsimp [stamp]
  omega

theorem stamp_inj {n a b} {i j : Fin (n+1)} (h : stamp a i = stamp b j) :
    a = b ∧ i = j := by
  have he : a = b := by
    rcases lt_trichotomy a b with h'|h'|h'
    · have := stamp_lt i j h'; omega
    · exact h'
    · have := stamp_lt j i h'; omega
  subst b
  exact ⟨rfl, Fin.ext (Nat.add_left_cancel h)⟩

@[simp] theorem stamp_nextRow {n} (a : ℕ) (i : Fin (n+1)) :
    stamp (a+1) i = stamp a i+(n+1) := by simp [stamp,Nat.add_mul]; omega
@[simp] theorem stamp_nextCol {n} (a : ℕ) (i : Fin n) :
    stamp a i.succ = stamp a i.castSucc+1 := by simp [stamp,Nat.add_assoc]

def birth {n k} : Core n k → ℕ
  | .inl (i,t) => stamp t.val i.succ
  | .inr (e,_,t) => stamp (e.val+1) t
def duration {n k} : Core n k → Bool → ℕ
  | .inl _, true => n+1
  | .inl _, false => 0
  | .inr _, _ => 1
def corePresent {n k} (s : ℕ) (p : Core n k × Bool) :=
  birth p.1 ≤ s ∧ s ≤ birth p.1 + duration p.1 p.2

def stage {n k} (j : Index n k) : ℕ :=
  stamp (j.1.val+1) (match j.2 with | .inl _ => 0 | .inr (i,_) => i.succ)
def slot {n k} (j : Index n k) : ℕ := match j.2 with | .inl a => a.val | .inr (_,a) => a.val

theorem slot_lt {n k} (j : Index n k) : slot j < 5 := by
  rcases j with ⟨e,a | ⟨i,a⟩⟩ <;> dsimp [slot] <;> omega

theorem stage_slot_inj {n k} (i j : Index n k) (hs : stage i = stage j) (hr : slot i = slot j) : i = j := by
  rcases i with ⟨e,a|⟨v,a⟩⟩ <;> rcases j with ⟨f,b|⟨u,b⟩⟩
  all_goals obtain ⟨h,h'⟩ := stamp_inj hs
  all_goals simp [slot] at hr
  all_goals simp [Fin.ext_iff] at h h'
  all_goals simp_all [Fin.ext_iff]

theorem present_incidence {n k} (s : Index n k) (u : Core n k) :
    (u ∈ before s → corePresent (stage s) (u,true)) ∧
    (u ∈ after s → corePresent (stage s) (u,false)) := by
  rcases s with ⟨e,j|⟨i,j⟩⟩
  all_goals
    fin_cases j <;> constructor <;> simp [before,after] <;>
      intro h <;> rcases h with (rfl|rfl) | rfl <;>
      simp [corePresent,birth,stage,duration,Fin.val_succ] <;> omega

private abbrev VarTip (n k : ℕ) := (Fin n × Fin (k+1)) × Bool
private abbrev SelTip (n k : ℕ) := (Fin k × Bool × Fin (n+1)) × Bool
private def varTip {n k} (v : VarTip n k) : Core n k × Bool := (.inl v.1,v.2)
private def selTip {n k} (v : SelTip n k) : Core n k × Bool := (.inr v.1,v.2)

private theorem var_width {n k} (s : ℕ) : Bounded (fun v : VarTip n k => corePresent s (varTip v)) (n+2) := by
  let old (v : VarTip n k) := v.2 = true ∧ stamp v.1.2.val v.1.1.succ < s ∧
    s ≤ stamp (v.1.2.val+1) v.1.1.succ
  let fresh (v : VarTip n k) := stamp v.1.2.val v.1.1.succ = s
  have ho : Bounded old n := by
    apply Bounded.byInj (fun v => v.1.1) _ (by simp)
    rintro ⟨⟨i,a⟩,b⟩ ⟨rfl,ha,ha'⟩ ⟨⟨j,c⟩,d⟩ ⟨rfl,hc,hc'⟩ h
    change i = j at h
    subst j
    dsimp only at ha hc ha' hc'
    have mono {a c : ℕ} (h : a ≤ c) : stamp a i.succ ≤ stamp c i.succ :=
      Nat.add_le_add_right (Nat.mul_le_mul_right _ h) _
    have he : a = c := by
      apply Fin.ext
      rcases lt_trichotomy a.val c.val with h|h|h
      · have := mono (show a.val+1 ≤ c.val from h); omega
      · exact h
      · have := mono (show c.val+1 ≤ a.val from h); omega
    rw [he]
  have hf : Bounded fresh 2 := by
    apply Bounded.byInj (fun v => v.2) _ (by simp)
    rintro ⟨⟨i,a⟩,b⟩ hi ⟨⟨j,c⟩,d⟩ hj hb
    obtain ⟨hr,hc⟩ := stamp_inj (hi.trans hj.symm)
    have ha : a = c := Fin.ext hr
    have hij : i = j := Fin.succ_inj.mp hc
    simp_all
  apply (ho.union hf).weaken _ le_rfl
  rintro ⟨⟨i,a⟩,b⟩ h
  cases b <;> simp [corePresent,varTip,birth,duration,old,fresh,stamp_nextRow] at h ⊢ <;> omega

private theorem sel_width {n k} (s : ℕ) : Bounded (fun v : SelTip n k => corePresent s (selTip v)) 8 := by
  apply Bounded.byInj (fun v => (decide (birth (selTip v).1 = s),v.1.2.1,v.2)) _ (by simp)
  rintro ⟨⟨e,b,t⟩,a⟩ h ⟨⟨f,c,u⟩,d⟩ h' eq
  simp only [selTip,birth,Prod.mk.injEq] at eq
  simp only [corePresent,selTip,birth,duration] at h h'
  obtain ⟨hd,hbc,had⟩ := eq
  have heq : stamp (e.val+1) t = s ↔ stamp (f.val+1) u = s := by simpa using (Bool.eq_iff_iff.mp hd)
  have hs : stamp (e.val+1) t = stamp (f.val+1) u := by omega
  obtain ⟨hef,htu⟩ := stamp_inj hs
  have : e = f := Fin.ext (by omega)
  simp_all

theorem core_width {n k} (s : ℕ) : Bounded (@corePresent n k s) (n+10) := by
  have h := ((var_width (n:=n) (k:=k) s).map varTip).union ((sel_width (n:=n) (k:=k) s).map selTip)
  apply h.weaken _ (by omega)
  rintro ⟨u|v,b⟩ hp
  · exact .inl ⟨(u,b),hp,rfl⟩
  · exact .inr ⟨(v,b),hp,rfl⟩

end Construction
end Parent

namespace Parent
namespace Construction

abbrev Time := ℕ ×ₗ (ℕ ×ₗ ℕ)
def moment (s j t : ℕ) : Time := toLex (s,toLex (j,t))
theorem moment_le {s j t r k u : ℕ} : moment s j t ≤ moment r k u ↔
    s < r ∨ s = r ∧ (j < k ∨ j = k ∧ t ≤ u) := by simp only [moment,Prod.Lex.toLex_le_toLex]

abbrev G (n k q l : ℕ) := Component.assembled (part n k q l)
noncomputable def partDraw (n k q l : ℕ) (s : Index n k) :
    Layout (part n k q l s).V (part n k q l s).edge (fun _ => False) 7 := by
  have weaken {A : Fragment (Tag n k l)} {w : ℕ} (a : A.Draw w) (h : w ≤ 7) :
      Layout A.V A.edge (fun _ => False) 7 :=
    ⟨a.stop,a.atV,a.limit,fun _ h => h.elim,a.meet,fun t => (a.small t).weaken (fun _ h => h) h⟩
  apply Classical.choice
  rcases s with ⟨e,j | ⟨i,j⟩⟩
  · fin_cases j <;> constructor
    all_goals first
      | exact weaken (Fragment.drawConst q).some (by decide)
      | exact weaken (Fragment.drawWeight ..) le_rfl
  · fin_cases j <;> constructor
    all_goals first
      | exact weaken (Fragment.drawConst q).some (by decide)
      | exact Layout.all _ _ ((Bounded.unit _).weaken (fun _ _ => trivial) (by decide))

def coreLo {n k} (p : Core n k × Bool) : Time := moment (birth p.1) 0 0
def coreHi {n k} (p : Core n k × Bool) : Time := moment (birth p.1+duration p.1 p.2) 5 0

theorem core_contact {n k} {p : Core n k × Bool} {s j t} (hp : corePresent s p) (hj : j < 5) :
    coreLo p ≤ moment s j t ∧ moment s j t ≤ coreHi p := by
  obtain ⟨h1,h2⟩ := hp
  simp only [coreLo,coreHi,moment_le]
  omega

noncomputable def hostLo {n k q l} (p : (G n k q l).V × Bool) : Time :=
  match p.1 with
  | .inl v => coreLo (v,p.2)
  | .inr ⟨s,v⟩ => moment (stage s) (slot s) (((partDraw n k q l s).atV v).lo)

noncomputable def hostHi {n k q l} (p : (G n k q l).V × Bool) : Time :=
  match p.1 with
  | .inl v => coreHi (v,p.2)
  | .inr ⟨s,v⟩ => moment (stage s) (slot s) (((partDraw n k q l s).atV v).hi)

theorem host_same {n k q l} (v : (G n k q l).V) (a b : Bool) : hostLo (v,a) ≤ hostHi (v,b) := by
  rcases v with u|⟨s,v⟩
  · simp [hostLo,hostHi,coreLo,coreHi,moment_le]
    omega
  · simpa [hostLo,hostHi,moment_le] using ((partDraw n k q l s).atV v).ord

theorem host_arc {n k q l} (v u : (G n k q l).V) (h : (G n k q l).edge v u) :
    hostLo (v,true) ≤ hostHi (u,false) ∧ hostLo (u,false) ≤ hostHi (v,true) := by
  cases h with
  | inner s v u h =>
    simpa [hostLo,hostHi,moment_le,Span.meets] using (partDraw n k q l s).meet v u h
  | enter s u v h =>
    have hp := (present_incidence s u).1 ((endpoints s u v).1 h)
    exact ⟨(core_contact (t:=_) hp (slot_lt s)).1,(core_contact hp (slot_lt s)).2⟩
  | leave s v u h =>
    have hp := (present_incidence s u).2 ((endpoints s u v).2 h)
    exact ⟨(core_contact hp (slot_lt s)).2,(core_contact hp (slot_lt s)).1⟩

theorem host_width {n k q l} (t : Time) :
    Bounded (fun p : (G n k q l).V × Bool => hostLo p ≤ t ∧ t ≤ hostHi p) (n+45) := by
  classical
  rcases t with ⟨s,j,t⟩
  let T := moment s j t
  let P (p : (G n k q l).V × Bool) := hostLo p ≤ T ∧ T ≤ hostHi p
  let f (p : Core n k × Bool) : (G n k q l).V × Bool := (Sum.inl p.1,p.2)
  have h1 := (core_width (n:=n) (k:=k) s).map f
  let Inner (p : (G n k q l).V × Bool) := ∃ (i : Index n k) (v : (part n k q l i).V),
    p.1 = .inr ⟨i,v⟩ ∧ P p
  have h2 : Bounded Inner 14 := by
    by_cases hh : ∃ i : Index n k, stage i = s ∧ slot i = j
    · obtain ⟨i,hsi,hji⟩ := hh
      let g (b : Bool) (v : (part n k q l i).V) : (G n k q l).V × Bool := (.inr ⟨i,v⟩,b)
      have H := (partDraw n k q l i).small t
      apply ((H.map (g false)).union (H.map (g true))).weaken _ le_rfl
      rintro ⟨z,b⟩ ⟨i',v,rfl,hp⟩
      change moment (stage i') (slot i') _ ≤ T ∧ T ≤ moment (stage i') (slot i') _ at hp
      simp only [T,moment_le] at hp
      have he : i' = i := stage_slot_inj i' i (by omega) (by omega)
      subst i'
      have hv : ((partDraw n k q l i).atV v).contains t := by
        unfold Span.contains
        constructor <;> omega
      cases b
      · exact .inl ⟨v,hv,rfl⟩
      · exact .inr ⟨v,hv,rfl⟩
    · apply Bounded.none.weaken _ (by decide)
      rintro ⟨z,b⟩ ⟨i,v,rfl,hp⟩
      change moment (stage i) (slot i) _ ≤ T ∧ T ≤ moment (stage i) (slot i) _ at hp
      simp only [T,moment_le] at hp
      exact hh ⟨i,by omega,by omega⟩
  apply (h1.union h2).weaken _ (by omega)
  rintro ⟨u|⟨i,v⟩,b⟩ hp
  · refine .inl ⟨(u,b),?_,rfl⟩
    change coreLo (u,b) ≤ T ∧ T ≤ coreHi (u,b) at hp
    simp only [T,coreLo,coreHi,moment_le] at hp
    change birth u ≤ s ∧ s ≤ birth u + duration u b
    constructor <;> omega
  · exact .inr ⟨i,v,rfl,hp⟩
end Construction
end Parent

namespace Parent

theorem compress {T : Type} [LinearOrder T] {m w : ℕ} (lo hi : Tip m → T)
    (width : ∀ t, Bounded (fun p => lo p ≤ t ∧ t ≤ hi p) w) :
    ∃ (l : ℕ) (a b : Tip m → Fin l), l ≤ 4*m+1 ∧
      (∀ p r, a p ≤ b r ↔ lo p ≤ hi r) ∧ ∀ t, Bounded (fun p => a p ≤ t ∧ t ≤ b p) w := by
  classical
  let points := Finset.univ.image lo ∪ Finset.univ.image hi
  have hcard : points.card ≤ 4*m+1 := by
    have h := (Finset.card_union_le (Finset.univ.image lo) (Finset.univ.image hi)).trans
      (Nat.add_le_add Finset.card_image_le Finset.card_image_le)
    simp only [Finset.card_univ,Tip,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at h
    dsimp [points]
    omega
  let ord := points.orderIsoOfFin rfl
  let a (p : Tip m) : points := ⟨lo p, Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))⟩
  let b (p : Tip m) : points := ⟨hi p, Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))⟩
  refine ⟨points.card,fun p => ord.symm (a p),fun p => ord.symm (b p),hcard,fun p r => ord.symm.le_iff_le,?_⟩
  intro t
  apply (width (ord t).1).weaken _ le_rfl
  intro v hv
  exact ⟨(ord.symm_apply_le).mp hv.1,(ord.le_symm_apply).mp hv.2⟩

namespace Network
variable {X : Type}
noncomputable def relOut (A : Network X) {m} (e : Fin m ≃ A.V) (i : Fin m) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun j => A.edge (e i) (e j))
noncomputable def relIn (A : Network X) {m} (e : Fin m ≃ A.V) (i : Fin m) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun j => A.edge (e j) (e i))
@[simp] theorem mem_out {A : Network X} {m} {e : Fin m ≃ A.V} {i j : Fin m} :
    j ∈ A.relOut e i ↔ A.edge (e i) (e j) := by classical simp [relOut]
@[simp] theorem mem_in {A : Network X} {m} {e : Fin m ≃ A.V} {i j : Fin m} :
    j ∈ A.relIn e i ↔ A.edge (e j) (e i) := by classical simp [relIn]

theorem models_card (A : Network X) {m} (e : Fin m ≃ A.V) (H : X → Bool)
    [DecidablePred (Models (A.relOut e) (fun i => A.on H (e i)))] :
    (Finset.univ.filter (Models (A.relOut e) (fun i => A.on H (e i)))).card =
    Fintype.card (A.State H) := by
  classical
  let F := Finset.univ.filter (Models (A.relOut e) (fun i => A.on H (e i)))
  have mem (f : Fin m → Bool) : f ∈ F ↔ Models (A.relOut e) (fun i => A.on H (e i)) f := by simp [F]
  let equiv : (↥F) ≃ A.State H := {
    toFun := fun f => ⟨fun v => f.1 (e.symm v), by
      obtain ⟨hz,ha⟩ := (mem _).1 f.2
      constructor
      · intro v h; exact hz _ (by simpa using h)
      · intro i j he hi hj hh
        exact ha _ _ (by simpa using hi) (by simpa using hj) (by simpa using he) hh⟩
    invFun := fun f => ⟨fun i => f.1 (e i), (mem _).2
      ⟨fun _ h => f.2.1 _ h, fun i j hi hj he => f.2.2 _ _ (mem_out.mp he) hi hj⟩⟩
    left_inv := fun f => Subtype.ext (funext (fun i => congrArg f.1 (e.symm_apply_apply i)))
    right_inv := fun f => Subtype.ext (funext (fun i => congrArg f.1 (e.apply_symm_apply i))) }
  have hh : F.card = Fintype.card (A.State H) := (Fintype.card_coe F).symm.trans (Fintype.card_congr equiv)
  convert! hh using 2
end Network

theorem Bounded.pullEquiv {V U : Type} {P : V → Prop} {w} (h : Bounded P w) (e : U ≃ V) :
    Bounded (fun i => P (e i)) w :=
  (h.map e.symm).weaken (fun i hi => ⟨e i,hi,e.symm_apply_apply i⟩) le_rfl

end Parent

namespace Parent.Network
theorem card_of_models {X : Type} (A : Network X) {m} (e : Fin m ≃ A.V) (H : X → Bool)
    (S : Finset (Fin m → Bool)) (hs : ∀ f, f ∈ S ↔ Models (A.relOut e) (fun i => A.on H (e i)) f) :
    S.card = Fintype.card (A.State H) := by
  classical
  have eq : S = Finset.univ.filter (Models (A.relOut e) (fun i => A.on H (e i))) := by
    ext f
    simpa using hs f
  exact (congrArg Finset.card eq).trans (models_card A e H)
end Parent.Network
open PEqualNP.Outside.L_lib_1218.Parent
open PEqualNP.Outside.L_lib_1218.Parent.Construction
set_option maxHeartbeats 700000 in
theorem Parent : (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ n k q : Nat, 2 ≤ q →
  let L := Nat.log2 q + 1
  ∃ (m : Nat) (nb : (Fin m × Bool) → Finset (Fin m × Bool))
    (source : Fin m → Option ((Fin k × Fin n × Bool) ⊕ (Fin k × Fin L))),
    m ≤ 81000*(n+1)*(k+1)*(L+1)^2 ∧
    (∀ p, p ∉ nb p ∧ (nb p).card ≤ 3) ∧
    (∀ p r, r ∈ nb p ↔ p ∈ nb r) ∧ (∀ p, ∀ r ∈ nb p, p.2 ≠ r.2) ∧
    (∀ i, (i,true) ∈ nb (i,false)) ∧
    (∃ (l : Nat) (bag : Fin l → Finset (Fin m × Bool)),
      l ≤ 4*m+1 ∧ (∀ t, (bag t).card ≤ n+45) ∧ (∀ p, ∃ t, p ∈ bag t) ∧
      (∀ p r, r ∈ nb p → ∃ t, p ∈ bag t ∧ r ∈ bag t) ∧
      ∀ p s t u, s ≤ t → t ≤ u → p ∈ bag s → p ∈ bag u → p ∈ bag t) ∧
    ∀ (lit : Fin k → Fin n → Bool → Bool) (weight : Fin k → Fin q),
      let code := fun e => ((weight e).val + q - 1) % q
      let active := fun i => (source i).elim true (Sum.elim
        (fun p => lit p.1 p.2.1 p.2.2)
        (fun p => !((code p.1).testBit p.2.val)))
      let live := (Finset.univ : Finset (Fin m × Bool)).filter (fun p => active p.1)
      let cover := fun (C : Finset (Fin m × Bool)) => C ⊆ live ∧
        ∀ p ∈ live, ∀ r ∈ nb p, r ∈ live → p ∈ C ∨ r ∈ C
      let opt := (Finset.univ : Finset (Finset (Fin m × Bool))).filter
        (fun C => cover C ∧ ∀ W, cover W → C.card ≤ W.card)
      let factor := fun (y : Fin n → Bool) (e : Fin k) =>
        if ∀ i, lit e i (y i) = false then (weight e).val else 1
      opt.Nonempty ∧ (∀ C ∈ opt, C.card =
        ((Finset.univ : Finset (Fin m)).filter (fun i => active i)).card) ∧
      opt.card % q = (∑ y : Fin n → Bool, ∏ e : Fin k, factor y e) % q) := by
  apply of_implication_host
  classical
  intro n k q hq
  let L := q.log2+1
  let A := G n k q L
  let m := Fintype.card A.V
  let e : Fin m ≃ A.V := (Fintype.equivFin A.V).symm
  let g : Tip m ≃ A.V × Bool := Equiv.prodCongr e (Equiv.refl _)
  let low (p : Tip m) := hostLo (g p)
  let high (p : Tip m) := hostHi (g p)
  have hw (t : Time) : Bounded (fun p => low p ≤ t ∧ t ≤ high p) (n+45) := (host_width t).pullEquiv g
  obtain ⟨l,lo,hi,hl,cmp,small⟩ := compress low high hw
  refine ⟨m,A.relOut e,A.relIn e,fun i => A.source (e i),l,lo,hi,host_size n k q hq,
    fun _ _ => Network.mem_out.trans Network.mem_in.symm,?_,?_,hl,?_,?_,?_,?_,?_⟩
  · intro i
    exact ((host_degree n k q L (e i)).2.pullEquiv e).card
  · intro i
    exact ((host_degree n k q L (e i)).1.pullEquiv e).card
  · rintro ⟨i,b⟩
    exact (cmp ..).2 (host_same (e i) b b)
  · intro t
    convert! (small t).card using 2
    ext p
    simp only [Finset.mem_filter]
  · intro i
    exact ⟨(cmp ..).2 (host_same (e i) false true),(cmp ..).2 (host_same (e i) true false)⟩
  · intro i j he
    have h := host_arc (e i) (e j) (Network.mem_out.mp he)
    exact ⟨(cmp ..).2 h.1,(cmp ..).2 h.2⟩
  · intro lit weight
    let H : Tag n k L → Bool := env lit weight
    dsimp only
    trans Fintype.card (A.State H) % q
    · apply congrArg (· % q)
      apply Network.card_of_models A e H
      intro f
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rfl
    · apply (host_count n k q hq lit weight).trans
      apply congrArg (· % q)
      apply Finset.sum_congr (by ext; simp)
      intro y _
      apply Finset.prod_congr (by ext; simp)
      intro j _
      by_cases hp : ∀ i, lit j i (y i) = false <;> simp [hp]

end Inlined

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem length_foldl (gs : List Gate) : ∀ w : List Bool,
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp [step]
    omega

def mapGate (r : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map r⟩

theorem rewire (m w : ℕ) (r : ℕ → ℕ) (hlo : ∀ i, i < m → r i < w + 2)
    (hhi : ∀ i, m ≤ i → r i = i - m + w) (gs : List Gate) :
    ∀ (a b : List Bool), m + 2 ≤ a.length → b.length + m = a.length + w →
      (∀ i, b.getD (r i) false = a.getD i false) →
      ∀ i, ((gs.map (mapGate r)).foldl step b).getD (r i) false
        = (gs.foldl step a).getD i false := by
  induction gs with
  | nil => intro a b _ _ h i; exact h i
  | cons g gs ih =>
    intro a b ha hab h i
    simp only [List.map_cons, List.foldl_cons]
    apply ih
    · simp [step]; omega
    · simp [step]; omega
    · intro j
      have hv : (mapGate r g).op.eval ((mapGate r g).inputs.map fun i => b.getD i false)
          = g.op.eval (g.inputs.map fun i => a.getD i false) := by
        simp only [mapGate, List.map_map]
        congr 1
        apply List.map_congr_left
        intro k _
        exact h k
      unfold step
      rw [hv]
      rcases lt_trichotomy j a.length with hj | hj | hj
      · have hr : r j < b.length := by
          by_cases hm : j < m
          · have := hlo j hm; omega
          · rw [hhi j (by omega)]; omega
        rw [List.getD_append _ _ _ _ hr, List.getD_append _ _ _ _ hj]
        exact h j
      · have hr : r j = b.length := by rw [hhi j (by omega)]; omega
        rw [hr, hj, List.getD_append_right _ _ _ _ le_rfl,
          List.getD_append_right _ _ _ _ le_rfl]
        simp
      · have hr : b.length < r j := by rw [hhi j (by omega)]; omega
        rw [List.getD_eq_default, List.getD_eq_default]
        · simp; omega
        · simp; omega

def accW (s o t : ℕ) : ℕ := if t = 0 then o else s + t - 1

theorem orchain (Wb : List Bool) (out : ℕ → ℕ) (n : ℕ) (hout : ∀ j ≤ n, out j < Wb.length) :
    ∀ t ≤ n,
      let W := ((List.range t).map fun t =>
        (⟨.or, [accW Wb.length (out 0) t, out (t+1)]⟩ : Gate)).foldl step Wb
      W.length = Wb.length + t ∧ (∀ i < Wb.length, W.getD i false = Wb.getD i false) ∧
      (W.getD (accW Wb.length (out 0) t) false = true ↔
        ∃ j ≤ t, Wb.getD (out j) false = true) := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨by simp, fun i _ => by simp, ?_⟩
    simp [accW]
  | succ t ih =>
    intro ht
    obtain ⟨hl, hp, ha⟩ := ih (by omega)
    dsimp only
    rw [List.range_succ, List.map_append, List.foldl_append]
    generalize hW : ((List.range t).map fun t =>
        (⟨.or, [accW Wb.length (out 0) t, out (t+1)]⟩ : Gate)).foldl step Wb = W at hl hp ha ⊢
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, step]
    refine ⟨by simp [hl]; omega, ?_, ?_⟩
    · intro i hi
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hp i hi
    · have e : accW Wb.length (out 0) (t+1) = W.length := by
        simp [accW, hl]
      rw [e, List.getD_append_right _ _ _ _ le_rfl]
      have h2 := hp _ (hout (t+1) ht)
      simp only [Nat.sub_self, List.getD_cons_zero, GateOp.eval, List.any_cons, List.any_nil,
        id, Bool.or_false, Bool.or_eq_true]
      rw [ha, h2]
      constructor
      · rintro (⟨j, hj, h⟩ | h)
        · exact ⟨j, by omega, h⟩
        · exact ⟨t+1, le_rfl, h⟩
      · rintro ⟨j, hj, h⟩
        rcases Nat.lt_or_ge j (t+1) with h' | h'
        · exact Or.inl ⟨j, by omega, h⟩
        · have : j = t+1 := by omega
          subst this
          exact Or.inr h

end PEqualNP.Outside.L_lib_1218

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_lib_1218

theorem PEqualNP.Outside.L_lib_1218 : (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ n k : Nat,
  let width := 2*k*n
  let satCount := fun (x : Fin width → Bool) =>
    ((Finset.univ : Finset (Fin n → Bool)).filter (fun y =>
      ∀ e : Fin k, ∃ i : Fin n,
        (List.ofFn x).getD (2*(e.val*n+i.val)+(y i).toNat) false = true)).card
  let valid := fun (d : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (d+2) C ∧
    C.output < d+2+C.size
  ∃ (m : Nat) (nb : (Fin m × Bool) → Finset (Fin m × Bool))
    (source : Fin m → Bool ⊕ Fin width),
    m ≤ 81000*(n+1)*(k+1)*(n+3)^2 ∧
    (∀ p, p ∉ nb p ∧ (nb p).card ≤ 3) ∧ (∀ p r, r ∈ nb p ↔ p ∈ nb r) ∧
    (∀ p, ∀ r ∈ nb p, p.2 ≠ r.2) ∧ (∀ i, (i,true) ∈ nb (i,false)) ∧
    (∃ (l : Nat) (bag : Fin l → Finset (Fin m × Bool)), l ≤ 4*m+1 ∧
      (∀ t, (bag t).card ≤ n+45) ∧ (∀ p, ∃ t, p ∈ bag t) ∧
      (∀ p r, r ∈ nb p → ∃ t, p ∈ bag t ∧ r ∈ bag t) ∧
      ∀ p s t u, s ≤ t → t ≤ u → p ∈ bag s → p ∈ bag u → p ∈ bag t) ∧
    let count := fun (mask : Fin m → Bool) =>
      let live := (Finset.univ : Finset (Fin m × Bool)).filter (fun p => mask p.1)
      let cover := fun (C : Finset (Fin m × Bool)) => C ⊆ live ∧
        ∀ p ∈ live, ∀ r ∈ nb p, r ∈ live → p ∈ C ∨ r ∈ C
      ((Finset.univ : Finset (Finset (Fin m × Bool))).filter
        (fun C => cover C ∧ ∀ W, cover W → C.card ≤ W.card)).card
    (∀ x : Fin width → Bool,
      count (fun i => (source i).elim id x) % 2^(n+1) = satCount x) ∧
    ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin (n+1) → Fin (m+2+C.size)),
      valid m C →
      (∀ mask : Fin m → Bool, ∀ j : Fin (n+1),
        (C.wires (List.ofFn mask ++ [false,true])).getD (tap j).val false =
          (count mask).testBit j.val) →
      ∃ (B : PEqualNP.CircuitLowerBounds.Circuit) (out : Fin (n+1) → Fin (width+2+B.size))
        (D : PEqualNP.CircuitLowerBounds.Circuit) (extra : List PEqualNP.CircuitLowerBounds.Gate),
        valid width B ∧ B.size = C.size ∧ B.gates.map (fun g => g.op) = C.gates.map (fun g => g.op) ∧
        valid width D ∧ D.gates = B.gates ++ extra ∧ extra.length ≤ n ∧
        (∀ g ∈ extra, g.op = .or ∧ g.inputs.length = 2) ∧
        ∀ x : Fin width → Bool,
          let inputs := List.ofFn x ++ [false,true]
          (∀ j : Fin (n+1), (B.wires inputs).getD (out j).val false = (satCount x).testBit j.val) ∧
          (D.eval inputs = true ↔ 0 < satCount x)) := by
  classical
  intro n k width satCount valid
  have hq : 2 ≤ 2^(n+1) := by
    calc 2 = 2^1 := rfl
      _ ≤ 2^(n+1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have H := PEqualNP.Outside.L_lib_1218.Parent n k (2^(n+1)) hq
  dsimp only at H
  obtain ⟨m, nb, source, hm, h1, h2, h3, h4, hbag, hsem⟩ := H
  have hL : Nat.log2 (2^(n+1)) + 1 + 1 = n + 3 := by rw [Nat.log2_two_pow]
  rw [hL] at hm
  have hidx : ∀ (e : Fin k) (i : Fin n) (b : Bool), 2*(e.val*n+i.val)+b.toNat < width := by
    intro e i b
    have h1 : e.val*n + i.val < k*n := by
      calc e.val*n+i.val < e.val*n + n := by have := i.isLt; omega
        _ = (e.val+1)*n := by ring
        _ ≤ k*n := Nat.mul_le_mul_right _ e.isLt
    have : b.toNat ≤ 1 := Bool.toNat_le b
    show _ < 2*k*n
    rw [Nat.mul_assoc]; omega
  let w0 : Fin (2^(n+1)) := ⟨0, by positivity⟩
  let src : Fin m → Bool ⊕ Fin width := fun i =>
    match source i with
    | none => Sum.inl true
    | some (Sum.inl p) =>
        Sum.inr ⟨2*(p.1.val*n+p.2.1.val)+p.2.2.toNat, hidx p.1 p.2.1 p.2.2⟩
    | some (Sum.inr p) =>
        Sum.inl (!(((w0.val + 2^(n+1) - 1) % 2^(n+1)).testBit p.2.val))
  refine ⟨m, nb, src, hm, h1, h2, h3, h4, hbag, ?_⟩
  intro count
  have hsat : ∀ x, satCount x < 2^(n+1) := by
    intro x
    refine lt_of_le_of_lt (Finset.card_le_univ _) ?_
    simp
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hcount : ∀ x : Fin width → Bool,
      count (fun i => (src i).elim id x) % 2^(n+1) = satCount x := by
    intro x
    obtain ⟨_, _, h⟩ := hsem (fun e i b => x ⟨_, hidx e i b⟩) (fun _ => w0)
    have hmask : (fun i => (src i).elim id x) = fun i => (source i).elim true (Sum.elim
        (fun p => x ⟨_, hidx p.1 p.2.1 p.2.2⟩)
        (fun p => !(((w0.val + 2^(n+1) - 1) % 2^(n+1)).testBit p.2.val))) := by
      funext i
      dsimp only [src]
      rcases source i with _ | (p | p) <;> rfl
    have hget : ∀ (e : Fin k) (i : Fin n) (b : Bool),
        (List.ofFn x).getD (2*(e.val*n+i.val)+b.toNat) false = x ⟨_, hidx e i b⟩ := by
      intro e i b
      rw [List.getD_eq_getElem _ _ (by simpa using hidx e i b), List.getElem_ofFn]
    have hsum : (∑ y : Fin n → Bool, ∏ e : Fin k,
        if ∀ i, x ⟨_, hidx e i (y i)⟩ = false then w0.val else 1) = satCount x := by
      symm
      dsimp only [satCount]
      rw [Finset.card_filter]
      refine Finset.sum_congr (by ext; simp) (fun y _ => ?_)
      symm
      by_cases hy : ∀ e : Fin k, ∃ i : Fin n,
          (List.ofFn x).getD (2*(e.val*n+i.val)+(y i).toNat) false = true
      · rw [if_pos hy]
        refine Finset.prod_eq_one (fun e _ => ?_)
        rw [if_neg]
        intro hf
        obtain ⟨i, hi⟩ := hy e
        rw [hget, hf i] at hi
        exact Bool.false_ne_true hi
      · rw [if_neg hy]
        push Not at hy
        obtain ⟨e, he⟩ := hy
        refine Finset.prod_eq_zero (Finset.mem_univ e) ?_
        rw [if_pos]
        intro i
        have := he i
        rw [hget] at this
        simpa using this
    have key : count (fun i => (src i).elim id x) % 2^(n+1)
        = (∑ y : Fin n → Bool, ∏ e : Fin k,
          if ∀ i, x ⟨_, hidx e i (y i)⟩ = false then w0.val else 1) % 2^(n+1) := by
      rw [hmask]
      dsimp only [count]
      convert h
    rw [key, hsum, Nat.mod_eq_of_lt (hsat x)]
  refine ⟨hcount, ?_⟩
  intro C tap hC hbits
  obtain ⟨hfan, hrb, hout⟩ := hC
  let r : ℕ → ℕ := fun i =>
    if h : i < m then (src ⟨i,h⟩).elim (fun b => width + b.toNat) (fun t => t.val)
    else i - m + width
  have hlo : ∀ i, i < m → r i < width + 2 := by
    intro i hi
    simp only [r, dif_pos hi]
    rcases src ⟨i,hi⟩ with b | t
    · have := Bool.toNat_le b
      simp only [Sum.elim_inl]; omega
    · have := t.isLt
      simp only [Sum.elim_inr]; omega
  have hhi : ∀ i, m ≤ i → r i = i - m + width := fun i hi => by
    simp only [r, dif_neg (not_lt.2 hi)]
  have hrlt : ∀ i t, i < m+2+t → r i < width+2+t := by
    intro i t h
    by_cases hm : i < m
    · have := hlo i hm; omega
    · rw [hhi i (by omega)]; omega
  let B : Circuit := ⟨C.gates.map (mapGate r), r C.output⟩
  have hBsize : B.size = C.size := by simp [B, Circuit.size]
  let o : ℕ → ℕ := fun j => if h : j < n+1 then r (tap ⟨j,h⟩).val else 0
  let extra : List Gate := (List.range n).map fun t =>
    (⟨.or, [accW (width+2+C.size) (o 0) t, o (t+1)]⟩ : Gate)
  let D : Circuit := ⟨B.gates ++ extra, accW (width+2+C.size) (o 0) n⟩
  have ho : ∀ j ≤ n, o j < width+2+C.size := by
    intro j hj
    simp only [o, dif_pos (Nat.lt_succ_of_le hj)]
    exact hrlt _ _ (tap _).isLt
  have hacc : ∀ t ≤ n, accW (width+2+C.size) (o 0) t < width+2+C.size+t := by
    intro t ht
    unfold accW
    split_ifs
    · have := ho 0 (by omega); omega
    · omega
  have hfanB : PEqualNP.MetaComplexity.FanInTwo B := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    simpa [mapGate] using hfan g0 hg0
  have hrbB : PEqualNP.MetaComplexity.NestedCover.ReadsBack (width+2) B := by
    intro j hj i hi
    have hj' : j < C.gates.length := by simpa [B] using hj
    have e1 : PEqualNP.MetaComplexity.NestedCover.gateAt B j
        = mapGate r (PEqualNP.MetaComplexity.NestedCover.gateAt C j) := by
      simp [PEqualNP.MetaComplexity.NestedCover.gateAt, B, hj']
    rw [e1] at hi
    obtain ⟨i0, hi0, rfl⟩ := List.mem_map.1 hi
    have := hrb j hj' i0 hi0
    exact hrlt _ _ (by omega)
  have hDsize : D.size = C.size + n := by simp [D, B, extra, Circuit.size]
  refine ⟨B, fun j => ⟨o j.val, by rw [hBsize]; exact ho _ (by omega)⟩, D, extra,
    ⟨hfanB, hrbB, by rw [hBsize]; exact hrlt _ _ hout⟩, hBsize,
    by simp [B, mapGate, Function.comp_def], ⟨?_, ?_, ?_⟩, rfl, by simp [extra], ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with h | h
    · exact hfanB g h
    · obtain ⟨t, _, rfl⟩ := List.mem_map.1 h
      simp
  · intro j hj i hi
    have hj2 : j < C.size + n := by rw [← hDsize]; exact hj
    by_cases h : j < B.gates.length
    · have e1 : PEqualNP.MetaComplexity.NestedCover.gateAt D j
          = PEqualNP.MetaComplexity.NestedCover.gateAt B j := by
        simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, D]
        exact List.getD_append _ _ _ _ h
      rw [e1] at hi
      exact hrbB j h i hi
    · have hlen : B.gates.length = C.size := hBsize
      obtain ⟨t, rfl⟩ : ∃ t, j = C.size + t := ⟨j - C.size, by omega⟩
      have ht : t < n := by omega
      have e1 : PEqualNP.MetaComplexity.NestedCover.gateAt D (C.size+t)
          = ⟨.or, [accW (width+2+C.size) (o 0) t, o (t+1)]⟩ := by
        simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, D]
        rw [List.getD_append_right _ _ _ _ (by omega), hlen, Nat.add_sub_cancel_left,
          List.getD_eq_getElem _ _ (by simpa [extra] using ht)]
        simp [extra]
      rw [e1] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · have := hacc t (by omega); omega
      · have := ho (t+1) (by omega); omega
  · rw [hDsize]
    have := hacc n le_rfl
    show accW (width+2+C.size) (o 0) n < _
    omega
  · intro g hg
    obtain ⟨t, _, rfl⟩ := List.mem_map.1 hg
    exact ⟨rfl, rfl⟩
  · intro x inputs
    have hrw : ∀ i, (B.wires inputs).getD (r i) false
        = (C.wires (List.ofFn (fun i => (src i).elim id x) ++ [false,true])).getD i false := by
      rw [wires_eq, wires_eq]
      refine rewire m width r hlo hhi C.gates _ _ (by simp) (by simp [inputs]; omega) ?_
      intro i
      by_cases hi : i < m
      · have hR : (List.ofFn (fun i => (src i).elim id x) ++ [false,true]).getD i false
            = (src ⟨i,hi⟩).elim id x := by
          rw [List.getD_eq_getElem _ _ (by simp; omega),
            List.getElem_append_left (by simpa using hi), List.getElem_ofFn]
        rw [hR]
        simp only [r, dif_pos hi]
        rcases src ⟨i,hi⟩ with b | t
        · simp only [Sum.elim_inl, id]
          dsimp only [inputs]
          rw [List.getD_append_right _ _ _ _ (by simp)]
          cases b <;> simp
        · simp only [Sum.elim_inr]
          dsimp only [inputs]
          rw [List.getD_eq_getElem _ _ (by simp; omega),
            List.getElem_append_left (by simp), List.getElem_ofFn]
      · have e1 : inputs.getD (i - m + width) false = [false,true].getD (i - m) false := by
          dsimp only [inputs]
          rw [List.getD_append_right _ _ _ _ (by simp), List.length_ofFn, Nat.add_sub_cancel]
        have e2 : (List.ofFn (fun i => (src i).elim id x) ++ [false,true]).getD i false
            = [false,true].getD (i - m) false := by
          rw [List.getD_append_right _ _ _ _ (by simp; omega), List.length_ofFn]
        rw [hhi i (by omega), e1, e2]
    have hbit : ∀ j : Fin (n+1), (B.wires inputs).getD (o j.val) false
        = (satCount x).testBit j.val := by
      intro j
      have : o j.val = r (tap j).val := by simp [o, Nat.le_of_lt_succ j.isLt]
      rw [this, hrw, hbits, ← hcount x, Nat.testBit_mod_two_pow]
      simp [Nat.le_of_lt_succ j.isLt]
    refine ⟨hbit, ?_⟩
    have hlen : (B.wires inputs).length = width+2+C.size := by
      rw [wires_eq, length_foldl]
      simp [inputs, B, Circuit.size]
    obtain ⟨_, _, hor⟩ := orchain (B.wires inputs) o n (by rw [hlen]; exact ho) n le_rfl
    rw [hlen] at hor
    have : D.eval inputs
        = (extra.foldl step (B.wires inputs)).getD (accW (width+2+C.size) (o 0) n) false := by
      simp only [Circuit.eval, wires_eq, D, List.foldl_append]
    rw [this, hor]
    constructor
    · rintro ⟨j, hj, h⟩
      rw [hbit ⟨j, by omega⟩] at h
      refine Nat.pos_of_ne_zero (fun h0 => ?_)
      rw [h0] at h
      simp at h
    · intro h
      obtain ⟨j, hj⟩ := Nat.exists_testBit_of_ne_zero (Nat.ne_of_gt h)
      have : j < n+1 := by
        by_contra hc
        have h5 := Nat.ge_two_pow_of_testBit hj
        have h6 : 2^(n+1) ≤ 2^j := Nat.pow_le_pow_right (by norm_num) (by omega)
        have := hsat x
        omega
      exact ⟨j, by omega, by rw [hbit ⟨j, this⟩]; exact hj⟩
