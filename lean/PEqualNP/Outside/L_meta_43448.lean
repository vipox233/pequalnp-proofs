import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_43448

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

abbrev W := BitVec 256

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 128 := ((x >>> 128) ^^^ x).setWidth 128
def cuts (ws : List W) : BitVec 128 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 128) ++ (0 : BitVec 128)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 128) (w : W) : Prop :=
  w.getLsbD (128+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 128) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 128+i.val < 256 := by omega
  have hi' : i.val < 256 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 128) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 128)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def insertW (x : W) : List W → List W
  | [] => [x]
  | y :: ys => if x.toNat ≤ y.toNat then x :: y :: ys else y :: insertW x ys

def canon : List W → List W
  | [] => []
  | x :: xs => insertW x (canon xs)

theorem insertW_perm (x : W) : ∀ l : List W, (insertW x l).Perm (x :: l)
  | [] => List.Perm.refl _
  | y :: ys => by
    unfold insertW
    split
    · exact List.Perm.refl _
    · exact ((insertW_perm x ys).cons y).trans (List.Perm.swap _ _ _)

theorem canon_perm : ∀ l : List W, (canon l).Perm l
  | [] => List.Perm.refl _
  | x :: xs => (insertW_perm x (canon xs)).trans ((canon_perm xs).cons x)

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (fun e l => optimized k e (canon l)) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (fun e l => optimized k e (canon l)) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        have hcn : (canon (z :: kept)).Perm (z :: kept) := canon_perm _
        apply dispatch_complete (k := k) (extra := extra) (fun e l => optimized k e (canon l)) hop hk (by omega) (by omega) (cuts_full hg hl)
        refine ih _ _ (hcn.nodup_iff.mpr hnd) ?_ (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl)
        rw [hcn.length_eq]; simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) (canon ws)

theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  have hcn : (canon ws).Perm ws := canon_perm ws
  have hopt : optimized n (n+1-ws.length) (canon ws) = true :=
    optimized_complete hg n (canon ws) _ (hcn.nodup_iff.mpr hnd) (by rw [hcn.length_eq]; omega) (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl')
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', hopt]⟩

def kidsOf (extra : ℕ) (a b : W) (r : List W) (w : W) : List (ℕ × List W) :=
  let v := sep w ||| cuts r
  (if v == -1 then [(extra, canon (w :: r))] else []) ++
  (if extra != 0 && (v ||| sep a == -1) then [(extra - 1, canon (w :: a :: r))] else []) ++
  (if extra != 0 && (v ||| sep b == -1) then [(extra - 1, canon (w :: b :: r))] else []) ++
  (if extra ≥ 2 && (v ||| sep a ||| sep b == -1) then [(extra - 2, canon (w :: a :: b :: r))] else [])

def children (c : ℕ × List W) : List (ℕ × List W) :=
  (pairs c.2).flatMap fun p => (ops p.1 p.2.1).flatMap fun w => kidsOf c.1 p.1 p.2.1 p.2.2 w

def goalFree (ws : List W) : Bool := !(ws == [goal] || ws == [~~~goal])

theorem dispatch_false {extra k : ℕ} {a b : W} {r : List W}
    (h : ∀ w ∈ ops a b, ∀ c ∈ kidsOf extra a b r w, optimized k c.1 c.2 = false) :
    dispatch extra (fun e l => optimized k e (canon l)) a b r = false := by
  unfold dispatch
  rw [List.any_eq_false]
  intro w hw hcon
  have h1 := h w hw
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne] at hcon
  rcases hcon with (⟨hv, hn⟩ | ⟨hx, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx, hv⟩, hn⟩
  · have := h1 (extra, canon (w :: r)) (by simp [kidsOf, hv])
    simp_all
  · have := h1 (extra - 1, canon (w :: a :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 1, canon (w :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 2, canon (w :: a :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all

theorem opt_false {k e : ℕ} {ws : List W} (hg : goalFree ws = true)
    (h : ∀ c ∈ children (e, ws), optimized k c.1 c.2 = false) :
    optimized (k + 1) e ws = false := by
  unfold optimized
  rw [Bool.or_eq_false_iff]
  refine ⟨by simpa [goalFree] using hg, ?_⟩
  rw [List.any_eq_false]
  rintro ⟨a, b, r⟩ hx hcon
  have key := dispatch_false (extra := e) (k := k) (a := a) (b := b) (r := r)
    (fun w hw c hc => h c (List.mem_flatMap.mpr ⟨(a, b, r), hx, List.mem_flatMap.mpr ⟨w, hw, hc⟩⟩))
  simp_all

def FalseAt (k : ℕ) (L : List (ℕ × List W)) : Prop := ∀ c ∈ L, optimized k c.1 c.2 = false

theorem falseAt_expand {k : ℕ} {L : List (ℕ × List W)}
    (hg : ∀ c ∈ L, goalFree c.2 = true) (h : FalseAt k (L.flatMap children)) : FalseAt (k + 1) L := by
  intro c hc
  exact opt_false (hg c hc) (fun c' hc' => h c' (List.mem_flatMap.mpr ⟨c, hc, hc'⟩))

def expandN : ℕ → List (ℕ × List W) → List (ℕ × List W)
  | 0, L => L
  | d + 1, L => expandN d (L.flatMap children)

def allGoalFree : ℕ → List (ℕ × List W) → Bool
  | 0, _ => true
  | d + 1, L => L.all (fun c => goalFree c.2) && allGoalFree d (L.flatMap children)

theorem falseAt_expandN : ∀ (d : ℕ) {j : ℕ} {L : List (ℕ × List W)},
    allGoalFree d L = true → FalseAt j (expandN d L) → FalseAt (j + d) L
  | 0, _, _, _, h => h
  | d + 1, j, L, hg, h => by
    simp only [allGoalFree, Bool.and_eq_true, List.all_eq_true] at hg
    exact falseAt_expand hg.1 (falseAt_expandN d hg.2 h)

def level0 (n : ℕ) (inputs : List W) : List (ℕ × List W) :=
  (inputs.sublists.filter (fun ws => decide (ws.length ≤ n + 1) && (cuts ws == -1))).map
    (fun ws => (n + 1 - ws.length, canon ws))

theorem search_of_false {n : ℕ} {inputs : List W} (h : FalseAt n (level0 n inputs)) :
    search n inputs = false := by
  unfold search
  rw [List.any_eq_false]
  intro ws hws hcon
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcon
  obtain ⟨⟨hl, hc⟩, ho⟩ := hcon
  have hmem : (n + 1 - ws.length, canon ws) ∈ level0 n inputs := by
    simp only [level0, List.mem_map, List.mem_filter]
    exact ⟨ws, ⟨hws, by simp [hl, hc]⟩, rfl⟩
  have := h _ hmem
  simp_all

theorem search_false_of_chunks {n d j : ℕ} {inputs : List W} (hj : j + d = n)
    (hg : allGoalFree d (level0 n inputs) = true)
    (hl : FalseAt j (expandN d (level0 n inputs))) : search n inputs = false := by
  subst hj
  exact search_of_false (falseAt_expandN d hg hl)

def chunkOK (j : ℕ) (L : List (ℕ × List W)) : Bool := L.all fun c => !optimized j c.1 c.2

theorem falseAt_of_chunkOK {j : ℕ} {L : List (ℕ × List W)} (h : chunkOK j L = true) : FalseAt j L := by
  intro c hc
  have := List.all_eq_true.mp h c hc
  simpa using this

def hashW (acc : ℕ) (w : W) : ℕ := (acc * 31 + w.toNat) % 1000003

def hashS (nb : ℕ) (c : ℕ × List W) : ℕ := (c.2.foldl hashW c.1) % nb

def inB (bk : List (List (ℕ × List W))) (c : ℕ × List W) : Bool :=
  (bk.getD (hashS bk.length c) []).any fun x => decide (x = c)

theorem inB_mem {bk : List (List (ℕ × List W))} {c : ℕ × List W} (h : inB bk c = true) :
    c ∈ bk.flatten := by
  unfold inB at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  rw [List.mem_flatten]
  by_cases hi : hashS bk.length x < bk.length
  · exact ⟨bk.getD (hashS bk.length x) [], by simp [List.getD_eq_getElem?_getD, hi], hx⟩
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)] at hx

def windowsF (j : ℕ) (L : List (List (ℕ × List W))) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => chunkOK j ((L.drop a).take s).flatten && windowsF j L (a + s) rest

theorem falseAt_of_windowsF {j : ℕ} {L : List (List (ℕ × List W))} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsF j L a sizes = true → FalseAt j (L.drop a).flatten
  | [], a, h => by
    intro c hc
    simp only [windowsF, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsF, Bool.and_eq_true] at h
    have h1 := falseAt_of_chunkOK h.1
    have h2 := falseAt_of_windowsF rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split, List.flatten_append] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsF_cons {j : ℕ} {L : List (List (ℕ × List W))} {a s : ℕ} {rest : List ℕ}
    (h1 : chunkOK j ((L.drop a).take s).flatten = true)
    (h2 : windowsF j L (a + s) rest = true) : windowsF j L a (s :: rest) = true := by
  simp [windowsF, h1, h2]

theorem windowsF_nil {j : ℕ} {L : List (List (ℕ × List W))} {a : ℕ} (h : (L.drop a).isEmpty = true) :
    windowsF j L a [] = true := h

theorem dispatch_mono {extra : ℕ} {n1 n2 : ℕ → List W → Bool} (a b : W) (r : List W)
    (h : ∀ e l, n2 e l = true → n1 e l = true) :
    dispatch extra n2 a b r = true → dispatch extra n1 a b r = true := by
  unfold dispatch
  simp only [List.any_eq_true]
  rintro ⟨w, hw, hx⟩
  refine ⟨w, hw, ?_⟩
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hx ⊢
  rcases hx with (⟨hv, hn⟩ | ⟨hx1, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx1, hv⟩, hn⟩
  · exact Or.inl (Or.inl ⟨hv, h _ _ hn⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inl ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inr ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inr ⟨⟨hx1, hv⟩, h _ _ hn⟩

def optB (S : ℕ × List W → Bool) : ℕ → ℕ → List W → Bool
  | 0, e, ws => S (e, ws)
  | k + 1, e, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch e (fun e' l => optB S k e' (canon l)) a b r)

theorem optB_sound (S : ℕ × List W → Bool) (J : ℕ)
    (hS : ∀ c, S c = false → optimized J c.1 c.2 = false) :
    ∀ (k e : ℕ) (ws : List W), optB S k e ws = false → optimized (J + k) e ws = false
  | 0, e, ws, h => hS (e, ws) h
  | k + 1, e, ws, h => by
    have ih := optB_sound S J hS k
    unfold optB at h
    rw [Bool.or_eq_false_iff] at h
    show optimized ((J + k) + 1) e ws = false
    unfold optimized
    rw [Bool.or_eq_false_iff]
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    rw [List.any_eq_false] at h2 ⊢
    rintro ⟨a, b, r⟩ hp hcon
    apply h2 (a, b, r) hp
    refine dispatch_mono a b r ?_ hcon
    intro e' l hl
    by_contra hne
    have hf : optB S k e' (canon l) = false := by simpa using hne
    have := ih e' (canon l) hf
    simp_all

def chunkB (S : ℕ × List W → Bool) (d : ℕ) (L : List (ℕ × List W)) : Bool :=
  L.all fun c => !optB S d c.1 c.2

def windowsG (f : List (ℕ × List W) → Bool) (L : List (ℕ × List W)) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => f ((L.drop a).take s) && windowsG f L (a + s) rest

theorem windowsG_sound {f : List (ℕ × List W) → Bool} {P : ℕ × List W → Prop}
    (hf : ∀ X, f X = true → ∀ c ∈ X, P c) {L : List (ℕ × List W)} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsG f L a sizes = true → ∀ c ∈ L.drop a, P c
  | [], a, h => by
    intro c hc
    simp only [windowsG, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsG, Bool.and_eq_true] at h
    have h1 := hf _ h.1
    have h2 := windowsG_sound hf rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsG_cons {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a s : ℕ} {rest : List ℕ}
    (h1 : f ((L.drop a).take s) = true) (h2 : windowsG f L (a + s) rest = true) :
    windowsG f L a (s :: rest) = true := by
  simp [windowsG, h1, h2]

theorem windowsG_nil {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a : ℕ}
    (h : (L.drop a).isEmpty = true) : windowsG f L a [] = true := h

theorem search_false_B {n dp J d : ℕ} {inputs : List W} {bk : List (List (ℕ × List W))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB bk c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB bk c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB bk c = true := by simpa using hc
    exact hBF c (inB_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB bk c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB bk c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem getD_mem_or_nil {α : Type} (l : List (List α)) (i : ℕ) :
    l.getD i [] ∈ l ∨ l.getD i [] = [] := by
  by_cases hi : i < l.length
  · left
    simp [List.getD_eq_getElem?_getD, hi]
  · right
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)]

def inB2 (g nb : ℕ) (bk2 : List (List (List (ℕ × List W)))) (c : ℕ × List W) : Bool :=
  ((bk2.getD (hashS nb c / g) []).getD (hashS nb c % g) []).any fun x => decide (x = c)

theorem inB2_mem {g nb : ℕ} {bk2 : List (List (List (ℕ × List W)))} {c : ℕ × List W}
    (h : inB2 g nb bk2 c = true) : c ∈ bk2.flatten.flatten := by
  unfold inB2 at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  have hG := getD_mem_or_nil bk2 (hashS nb x / g)
  have hB := getD_mem_or_nil (bk2.getD (hashS nb x / g) []) (hashS nb x % g)
  rw [List.mem_flatten]
  rcases hB with hB | hB
  · rcases hG with hG | hG
    · exact ⟨_, List.mem_flatten.mpr ⟨_, hG, hB⟩, hx⟩
    · rw [hG] at hB
      simp at hB
  · rw [hB] at hx
    simp at hx

theorem search_false_B2 {n dp J d g nb : ℕ} {inputs : List W} {bk2 : List (List (List (ℕ × List W)))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk2.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g nb bk2 c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk2.flatten.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB2 g nb bk2 c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g nb bk2 c = true := by simpa using hc
    exact hBF c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem search_false_C2 {n dp J d g1 nb1 g2 nb2 : ℕ} {inputs : List W}
    {bkA bkB : List (List (List (ℕ × List W)))} {sa sb sc : List ℕ}
    (hj : J + 1 + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hC : windowsF J bkB.flatten 0 sc = true)
    (hB : windowsG (chunkB (fun c => !inB2 g2 nb2 bkB c) 1) bkA.flatten.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g1 nb1 bkA c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hCF : FalseAt J bkB.flatten.flatten := by
    have := falseAt_of_windowsF sc 0 hC
    simpa using this
  have hS2 : ∀ c, (fun c => !inB2 g2 nb2 bkB c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g2 nb2 bkB c = true := by simpa using hc
    exact hCF c (inB2_mem hin)
  have hP2 : ∀ c ∈ bkA.flatten.flatten, optimized (J + 1) c.1 c.2 = false := by
    have h1 : ∀ c ∈ (bkA.flatten.flatten).drop 0, optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false := by
      refine windowsG_sound (P := fun c => optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false) ?_ sb 0 hB
      intro X hX c hc
      have := List.all_eq_true.mp hX c hc
      simpa using this
    intro c hc
    exact optB_sound _ J hS2 1 c.1 c.2 (h1 c (by simpa using hc))
  have hS1 : ∀ c, (fun c => !inB2 g1 nb1 bkA c) c = false → optimized (J + 1) c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g1 nb1 bkA c = true := by simpa using hc
    exact hP2 c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + 1 + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ (J + 1) hS1 d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + 1 + d) (d := dp) hj hg hF

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 256 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 256)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 256) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 256) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 256) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#256)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k (~~~goal)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
    · exact ⟨t, .inr eq.symm, ht⟩
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (~~~goal) := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4276808426 * 2 ^ 32 + 4240500864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

theorem bound_from_search (inputs : List W) (width : inputs.length = 6)
    (nd : inputs.Nodup) (reject : search 8 inputs = false)
    (sample : ∀ k : Fin 256,
      target (fun i => (inputs.getD i.val 0)[k.val]) = (~~~goal)[k.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target x) :
    8 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 256) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 6) : Bool := bit k (inputs.getD i.val 0)
    have same : List.ofFn x = inputs.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < inputs.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (inputs.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample k
  obtain ⟨t, ht, run⟩ := compile gs o hg inputs inputs.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t b inputs.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact Bool.noConfusion (reject.symm.trans (search_complete ht 8 inputs nd (lift low run)))

def rows : List W :=
  [(0x0115042b8c6036ea#64 ++ 0x00045410ae3180db#64 ++ 0x033f3c7f8c607ffd#64 ++ 0x940cfcf1fe3181ff#64 : BitVec 256),
   (0x0c4c519805ad8b4c#64 ++ 0x043131466016b62d#64 ++ 0x1cccd3980fff8ffb#64 ++ 0xbc73334e603ffe3f#64 : BitVec 256),
   (0x60b0a2e0b056d1b0#64 ++ 0x0982c28b82c15b46#64 ++ 0xe0f0e3e1f07ff1f7#64 ++ 0xdf83c38f87c1ffc7#64 : BitVec 256),
   (0xb700fc015a836c00#64 ++ 0x22dc03f0056a0db0#64 ++ 0xff00fc01ff83fe2f#64 ++ 0xeffc03f007fe0ff8#64 : BitVec 256),
   (0xdbff0001ef780000#64 ++ 0x436ffc0007bde000#64 ++ 0xffff0001fffc001f#64 ++ 0xebfffc0007fff000#64 : BitVec 256),
   (0xfeeafb5400000000#64 ++ 0x13fbabed50000000#64 ++ 0xfffffffe0000003f#64 ++ 0x73fffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 4]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [9, 3]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [10, 5]⟩, ⟨.and, [8, 12]⟩, ⟨.and, [11, 6]⟩, ⟨.or, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x011500218c6010a0 0x0004540086318042 0x033f20618c6071fd 0x940cfc81863181c7

def z1 : W := mkw 0x0115042b8c6036ea 0x00045410ae3180db 0x033f3c7f8c607ffd 0x940cfcf1fe3181ff

def z2 : W := mkw 0x0c4c519805ad8b4c 0x043131466016b62d 0x1cccd3980fff8ffb 0xbc73334e603ffe3f

def z3 : W := mkw 0x60b0a2e0b056d1b0 0x0982c28b82c15b46 0xe0f0e3e1f07ff1f7 0xdf83c38f87c1ffc7

def z4 : W := mkw 0xb700fc015a836c00 0x22dc03f0056a0db0 0xff00fc01ff83fe2f 0xeffc03f007fe0ff8

def z5 : W := mkw 0xdbff0001ef780000 0x436ffc0007bde000 0xffff0001fffc001f 0xebfffc0007fff000

def z6 : W := mkw 0xfeeafb5400000000 0x13fbabed50000000 0xfffffffe0000003f 0x73fffffff8000000

def z7 : W := mkw 0x00110022804010a2 0x000044008a010042 0x0033006600000000 0x0000cc0198000000

def z8 : W := mkw 0xdbff042bef7836ea 0x436ffc10afbde0db 0xffff3c7ffffc7fff 0xfffffcf1fffff1ff

def z9 : W := mkw 0xf7b0fee1fad7fdb0 0x2bdec3fb87eb5ff6 0xfff0ffe1ffffffff 0xffffc3ff87ffffff

def z10 : W := mkw 0x0111042b884036ea 0x00044410ae2100db 0x03333c7f80007fe4 0x140cccf1fe0001ff

def z11 : W := mkw 0xbf4cfc015fab6c00 0x22fd33f0057eadb0 0xffccfc01fffffe3f 0xefff33f007fffff8

def z12 : W := mkw 0xb300ac015a026400 0x22cc02b005680990 0xff002c01ff80700f 0xebfc00b007fe01c0

def z13 : W := mkw 0x0c4c519805ad8b4c 0x043131466016b62d 0x1c0c10180fff8fc8 0xac703040603ffe3f

def z14 : W := mkw 0x2400fc0010836c00 0x209003f000420db0 0x0000fc000003fe20 0x040003f000000ff8

def z15 : W := mkw 0xfffffc01fffb6c00 0x63fffff007ffedb0 0xfffffc01fffffe3f 0xeffffff007fffff8

def z16 : W := mkw 0x60b0a2e0b056d1b0 0x0982c28b82c15b46 0xe0f0e3e1f01ff006 0x4b83c38f87c07fc0

def z17 : W := mkw 0x01110423884034a2 0x000444108e2100d2 0x03332c6780007004 0x000cccb19e0001c0

def z18 : W := mkw 0x0d5d55bb8dedbfee 0x04357556ee37b6ff 0x1fffffff8fffffff 0xbc7ffffffe3fffff

def z19 : W := mkw 0xb600f80000000000 0x02d803e000000000 0xff00fc000000002f 0x63fc03f000000000

def z20 : W := mkw 0xdaea000063180000 0x436ba800018c6000 0xfcc00000739c0002 0x6bf3000001ce7000

def z21 : W := mkw 0xdeee519867bd8b4c 0x477bb946619ef62d 0xfcccd3987fff8ffb 0xfff3334e61fffe3f

def z22 : W := mkw 0x0c4c519805ad8b4c 0x043131466016b62d 0x00ccd398007f8ff0 0x1403334e6001fe3f

def z23 : W := mkw 0x010000014a000000 0x0004000005280000 0x00000001ff800000 0x8800000007fe0000

def z24 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z25 : W := mkw 0x00100020804010a0 0x0000400082010042 0x00300060006001d0 0x1000c00180018007

def z26 : W := mkw 0x93150001ef780000 0x424c540007bde000 0xff000001fffc000f 0xebfc000007fff000

def z27 : W := mkw 0xdaea000000000000 0x036ba80000000000 0xffff00000000001f 0x63fffc0000000000

def z28 : W := mkw 0xfffffb55ef780000 0x53ffffed57bde000 0xfffffffffffc003f 0xfbfffffffffff000

def z29 : W := mkw 0x2010a020904250a0 0x0080428082410942 0xe030e061f063f1f7 0xdf80c38187c18fc7

def z30 : W := mkw 0x0000008000048100 0x0000000200001204 0x00c0c380007f81f3 0x9c03030e0001fe07

def z31 : W := mkw 0x60b0a260b05250b0 0x0982c28982c14942 0xe0302061f0007004 0x4380c08187c001c0

def z32 : W := mkw 0x9600580000000000 0x0258016000000000 0x1f001c0000000008 0x207c007000000000

def z33 : W := mkw 0x0004008805ad8b4c 0x040010022016b62d 0x000000000fff8fc0 0x8c000000003ffe3f

def z34 : W := mkw 0xfeeafb5400000000 0x13fbabed50000000 0xfcffc3fe00000012 0x73f3ff0ff8000000

def z35 : W := mkw 0xdaea000000000000 0x036ba80000000000 0xffff3c7e0000003f 0x73fffcf1f8000000

def z36 : W := mkw 0x0404519804a58b4c 0x041011466012962d 0x000cd3980c638ff9 0x9400334e60318e3f

def z37 : W := mkw 0x6cfcf3f8b5ffdbfc 0x0db3f3cfe2d7ff6f 0xfcfcf3f9ffffffff 0xfff3f3cfe7ffffff

def z38 : W := mkw 0x0000008800858b4c 0x040000022002162d 0x0000000000038fc0 0x0400000000000e3f

def z39 : W := mkw 0x0c48511000000000 0x0031214440000000 0x1cccd3980000003b 0x3073334e60000000

def z40 : W := mkw 0x2400fee01087fdb0 0x289003fb80421ff6 0x0000ffe00003ffe0 0x140003ff80000fff

def z41 : W := mkw 0x40b00000a0500000 0x0102c00002814000 0xe0f00001f07c0017 0xcb83c00007c1f000

def z42 : W := mkw 0x9b4f00014f280000 0x426d3c00053ca000 0x1f0f00000f800008 0x207c3c00003e0000

def z43 : W := mkw 0xb311ac23da4274a2 0x22cc46b08f6909d2 0xe3332c67f0007004 0x438cccb19fc001c0

def z44 : W := mkw 0x0c4c519005ad8904 0x043131464016b624 0x1cccc3800fff801b 0xa873330e003ffe00

def z45 : W := mkw 0x9200000042000000 0x0248000001080000 0xfc00000073800002 0x6bf0000001ce0000

def z46 : W := mkw 0x0115042b8c6036ea 0x00045410ae3180db 0x000000018c607fc0 0x84000000063181ff

def z47 : W := mkw 0x2400fb5400000000 0x109003ed50000000 0x0000fffe00000020 0x100003fff8000000

def z48 : W := mkw 0x084c000005280000 0x002130000014a000 0x1ccc00000ffc001b 0xa8733000003ff000

def z49 : W := mkw 0x2000a2e01006d1b0 0x0880028b80401b46 0x0000e3e00003f1e0 0x1400038f80000fc7

def z50 : W := mkw 0xdbef00014f280000 0x436fbc00053ca000 0xffff00000f80001f 0x63fffc00003e0000

def z51 : W := mkw 0x2100a4015a836c00 0x20840290056a0db0 0xe000e001ff83fe27 0xcf80038007fe0ff8

def z52 : W := mkw 0xb600f80052834800 0x22d803e0014a0d20 0xfc00e001f383f027 0xeff0038007ce0fc0

def z53 : W := mkw 0xb600f80052834800 0x22d803e0014a0d20 0xfc00c00073838002 0x6bf0030001ce0e00

def z54 : W := mkw 0xb715fc2bdee37eea 0x22dc57f0af7b8dfb 0xff3ffc7fffe3ffff 0xfffcfff1ffff8fff

def z55 : W := mkw 0xdfff5199effd8b4c 0x477ffd4667bff62d 0xffffd399ffff8fff 0xffffff4e67fffe3f

def z56 : W := mkw 0xf2a2aa4400000000 0x13ca8aa910000000 0xe3332c6600000004 0x438cccb198000000

def z57 : W := mkw 0xfffafff5fad7fdb0 0x3bffebffd7eb5ff6 0xffffffffffffffff 0xffffffffffffffff

def z58 : W := mkw 0x0004000804200248 0x0000100020108009 0x000c10180c600ff9 0x940030406031803f

def z59 : W := mkw 0x0000000000000000 0x0000000000000000 0x03332c6600000004 0x000cccb198000000

def z60 : W := mkw 0x011500018c600000 0x0004540006318000 0x033f00018c60001d 0x800cfc0006318000

def z61 : W := mkw 0x0400519800858b4c 0x041001466002162d 0x0000d39800038fe0 0x1400034e60000e3f

def z62 : W := mkw 0xfbffa001ff7a4000 0x43effe8007fde900 0xffffe001fffff03f 0xefffff8007ffffc0

def z63 : W := mkw 0x40b002e0a05491b0 0x0902c00b82815246 0x00f003e0007c01d0 0x1003c00f8001f007

def z64 : W := mkw 0x97005c014a812c00 0x225c0170052a04b0 0x1f001c000f800e08 0x207c0070003e0038

def z65 : W := mkw 0xfbffa2e1ff7ed1b0 0x4beffe8b87fdfb46 0xffffe3e1fffff1ff 0xffffff8f87ffffc7

def z66 : W := mkw 0x001400a8b5ffdbfc 0x0c005002a2d7ff6f 0x00000001ffffffc0 0x8c00000007ffffff

def z67 : W := mkw 0xdbff0009ef780248 0x436ffc0027bde009 0xffff1019fffc0fff 0xfffffc4067fff03f

def z68 : W := mkw 0x60a0a24000000000 0x0182828900000000 0xe0f0e3e000000037 0x5383c38f80000000

def z69 : W := mkw 0xfefafbf4b056d1b0 0x1bfbebefd2c15b46 0xfffffffff07ff1ff 0xffffffffffc1ffc7

def z70 : W := mkw 0x085d01ba856c93ee 0x04217406ea15b24f 0x00ff03fe007c01d0 0x1003fc0ff801f007

def z71 : W := mkw 0xdaee000067380000 0x436bb800019ce000 0xfccc00007ffc001b 0xebf3300001fff000

def z72 : W := mkw 0x9b5f0001cf680000 0x426d7c00073da000 0x1f3f00018fe0001d 0xa07cfc00063f8000

def z73 : W := mkw 0x084c0198052c834c 0x042130066014b20d 0x00cc0398007c01d0 0x1003300e6001f007

def z74 : W := mkw 0x2000ac0010026400 0x208002b000400990 0x00002c0000007000 0x000000b0000001c0

def z75 : W := mkw 0xfeeefbdc05ad8b4c 0x17fbbbef7016b62d 0xfcccd3980fff8ffb 0xfff3334e603ffe3f

def z76 : W := mkw 0xfeeefbdc05ad8b4c 0x17fbbbef7016b62d 0xfffffffe0fff8fff 0xfffffffff83ffe3f

def z77 : W := mkw 0xdfff55bbeffdbfee 0x477ffd56efbff6ff 0xffffffffffffffff 0xffffffffffffffff

def z78 : W := mkw 0x61b1a663b85274b2 0x0986c6998ee149d2 0xe3332c67f0007004 0x438cccb19fc001c0

def z79 : W := mkw 0x2400fb5400000000 0x109003ed50000000 0x033ffffe0000003d 0x100cfffff8000000

def z80 : W := mkw 0x9a4a000000000000 0x0269280000000000 0x1f0f000000000008 0x207c3c0000000000

def z81 : W := mkw 0x0100040108002400 0x0004001004200090 0x03003c018c007e2d 0x840c00f0063001f8

def z82 : W := mkw 0xdbff0001ef780000 0x436ffc0007bde000 0xfcc00001fffc0002 0xebf3000007fff000

def z83 : W := mkw 0x2010a2e0b056d1b0 0x0880428b82c15b46 0x0000e3e1f07ff1e0 0x9c00038f87c1ffc7

def z84 : W := mkw 0x00100020804010a0 0x0000400082010042 0x00302061806071f5 0x9400c081860181c7

def z85 : W := mkw 0x61b5a6ebbc76f7fa 0x0986d69baef1dbdf 0xe3fffffffc7fffff 0xdf8ffffffff1ffff

def z86 : W := mkw 0x010004015a836c00 0x20040010056a0db0 0x00000001ff83fe00 0x8c00000007fe0ff8

def z87 : W := mkw 0x48ea035400000000 0x1123a80d50000000 0x00ff03fe00000010 0x1003fc0ff8000000

def z88 : W := mkw 0x0400519000858904 0x0410014640021624 0x0000c38000038000 0x0000030e00000e00

def z89 : W := mkw 0x9f4c5d194fa92e4c 0x267d3174653ea4b9 0x1f0c1c180f800e08 0x207c3070603e0038

def z90 : W := mkw 0xbf4cfd995fafef4c 0x26fd33f6657ebfbd 0xffccff99ffffffff 0xffff33fe67ffffff

def z91 : W := mkw 0x60b0a2e0b056d1b0 0x0982c28b82c15b46 0xe030e3e1f003f1e4 0x5780c38f87c00fc7

def z92 : W := mkw 0x930004015a836c00 0x224c0010056a0db0 0xff000001ff83fe0f 0xeffc000007fe0ff8

def z93 : W := mkw 0xfffffb55ef780000 0x53ffffed57bde000 0xffffc381fffc001f 0xebffff0e07fff000

def z94 : W := mkw 0x00100020b05250b0 0x0800400082c14942 0x00000001f0007000 0x0000000007c001c0

def z95 : W := mkw 0xfefafb74804010a0 0x13fbebedd2010042 0xffffffff806071ff 0xf7fffffffe0181c7

def z96 : W := mkw 0x9e4a591400000000 0x1279296450000000 0x1f3f3c7e0000003d 0x307cfcf1f8000000

def z97 : W := mkw 0x0000000000000000 0x0000000000000000 0x033f3c7e0000003d 0x100cfcf1f8000000

def z98 : W := mkw 0xfeeefbdc052c834c 0x17fbbbef7014b20d 0xfffffffe007c01ff 0x73fffffff801f007

def z99 : W := mkw 0x0400500000810800 0x0010014000020420 0x1c00d0000f838e2b 0xac700340003e0e38

def z100 : W := mkw 0xb300ac015a026400 0x22cc02b005680990 0xe3002c01f0007004 0x438c00b007c001c0

def z101 : W := mkw 0x0400591400000000 0x1010016450000000 0x00001c1e00000000 0x0000007078000000

def z102 : W := mkw 0x0500540108812c00 0x00140150042204b0 0x1f00fc018f83fe2f 0xac7c03f0063e0ff8

def z103 : W := mkw 0x0000000000810800 0x0000000000020420 0x000000000f838e00 0x8c000000003e0e38

def z104 : W := mkw 0x084c0198052c834c 0x042130066014b20d 0x00cc13980c7c0ff9 0x9403304e6031f03f

def z105 : W := mkw 0x68fca3f8b57ed3fc 0x0da3f28fe2d5fb4f 0xe0fce3f9f07ff1f7 0xdf83f38fe7c1ffc7

def z106 : W := mkw 0xfeeafb5400000000 0x13fbabed50000000 0xfcccd3980000003b 0x73f3334e60000000

def z107 : W := mkw 0x0015002a846012ea 0x00005400aa11804b 0x003f007e006001d0 0x1000fc01f8018007

def z108 : W := mkw 0x084f000005280000 0x40213c000014a000 0x000f000000000000 0x00003c0000000000

def z109 : W := mkw 0x40a0000000000000 0x0102800000000000 0xe0f0000000000017 0x4383c00000000000

def z110 : W := mkw 0x00100000a0500000 0x0000400002814000 0x00000001f07c0000 0x8800000007c1f000

def z111 : W := mkw 0x930000014a000000 0x024c000005280000 0xff000001ff80000f 0xebfc000007fe0000

def z112 : W := mkw 0xffffff55fffb6c00 0x73fffffd57ffedb0 0xfffffffffffffe3f 0xfffffffffffffff8

def z113 : W := mkw 0x0000000000000000 0x0000000000000000 0x000010000c000e29 0x8400004000300038

def z114 : W := mkw 0xdbff0423ef7834a2 0x436ffc108fbde0d2 0xffff2c67fffc701f 0xebfffcb19ffff1c0

def z115 : W := mkw 0xdafa0000e3580000 0x436be800038d6000 0xfcf00001f3fc0017 0xebf3c00007cff000

def z116 : W := mkw 0x0105040b0c20264a 0x000414102c308099 0x030f1c1e0c000e08 0x000c3c7078300038

def z117 : W := mkw 0x2500fc015a836c00 0x209403f0056a0db0 0x0000fc01ff83fe20 0x8c0003f007fe0ff8

def z118 : W := mkw 0xdfff5001eff90800 0x437ffd4007bfe420 0xffffd001ffff8e3f 0xefffff4007fffe38

def z119 : W := mkw 0x9b5f042bcf6836ea 0x426d7c10af3da0db 0x1f3f3c7f8fe07ffd 0xb47cfcf1fe3f81ff

def z120 : W := mkw 0xf3b3ac01fa526400 0x63ceceb007e94990 0xe3332c01f0007004 0x438cccb007c001c0

def z121 : W := mkw 0xdaff0000e7780000 0x436bfc00039de000 0xfcff000073fc0012 0x6bf3fc0001cff000

def z122 : W := mkw 0xffffff7f8c6036ea 0x13fffffdfe3180db 0xffffffff8c607fff 0xf7fffffffe3181ff

def z123 : W := mkw 0x2000a00010024000 0x0080028000400900 0xe000e001f003f027 0xcf80038007c00fc0

def z124 : W := mkw 0x48fc0000a5780000 0x0123f0000295e000 0xfcfc0001fffc001f 0xebf3f00007fff000

def z125 : W := mkw 0x011500098c600248 0x0004540026318009 0x033f10198c600ffd 0x940cfc406631803f

def z126 : W := mkw 0xfeeafbd4018d8904 0x17fbabef50063624 0xfcc0c380039f8002 0x6bf3030e000e7e00

def z127 : W := mkw 0x001000a0b056d1b0 0x0800400282c15b46 0x00000001f07ff1c0 0x8c00000007c1ffc7

def z128 : W := mkw 0x60a0a24000000000 0x0182828900000000 0xe3fffffe0000003f 0x538ffffff8000000

def z129 : W := mkw 0x0c4c519805ad8b4c 0x043131466016b62d 0x1ffffffe0fff8fff 0xbc7ffffff83ffe3f

def z130 : W := mkw 0xf3b0ae61fa5274b0 0x2bcec2b987e949d2 0xe3302c61f0007004 0x438cc0b187c001c0

def z131 : W := mkw 0xdeee519805ad8b4c 0x077bb9466016b62d 0xffffd3980fff8fff 0xffffff4e603ffe3f

def z132 : W := mkw 0x00000422000034a2 0x00000010880000d2 0x00002c6600007000 0x000000b1980001c0

def z133 : W := mkw 0x40b502eaa47493fa 0x0902d40baa91d24f 0x00ff03fe007c01d0 0x1003fc0ff801f007

def z134 : W := mkw 0xbe48f990538fc904 0x26f923e6414e3f24 0xfcc0c380739f8002 0x6bf3030e01ce7e00

def z135 : W := mkw 0x0d5d553b8c6036ea 0x00357554ee3180db 0x1fffffff8c607fff 0xb47ffffffe3181ff

def z136 : W := mkw 0xb710fca1fad7fdb0 0x2adc43f287eb5ff6 0xff00fc01ffffffef 0xeffc03f007ffffff

def z137 : W := mkw 0xb700fc2b5a837eea 0x22dc03f0ad6a0dfb 0xff00fc7fff83ffef 0xfffc03f1fffe0fff

def z138 : W := mkw 0xb700fc015a836c00 0x22dc03f0056a0db0 0xff3ffc7fff83fe3f 0xfffcfff1fffe0ff8

def z139 : W := mkw 0xf2b2aae4b056d1b0 0x1bcacaab92c15b46 0xe3f3efe7f07ff1f7 0xdf8fcfbf9fc1ffc7

def z140 : W := mkw 0xdbff0001ef780000 0x436ffc0007bde000 0x1fff00000ffc0018 0x207ffc00003ff000

def z141 : W := mkw 0x0404519805ad8b4c 0x041011466016b62d 0x0000d3980fff8fe0 0x9c00034e603ffe3f

def z142 : W := mkw 0x6cf8f3f0b1dfd9b4 0x0db3e3cfc2c77f66 0xfcf0e3e1f3fff1f7 0xfff3c38f87cfffc7

def z143 : W := mkw 0x0115042b8c6036ea 0x00045410ae3180db 0x033f1c7e0c600fd8 0x100cfc71f831803f

def z144 : W := mkw 0x40a0024000000000 0x0102800900000000 0x00f003e000000010 0x1003c00f80000000

def z145 : W := mkw 0xfeeefb5c04200248 0x13fbbbed70108009 0xfffffffe0c600fff 0xf7fffffff831803f

def z146 : W := mkw 0x0c4c511805a90a4c 0x043131446016a429 0x1c0c10180f800e08 0x20703040603e0038

def z147 : W := mkw 0x48fc03f8a57c93fc 0x0d23f00fe295f24f 0x00fc03f8007c01d0 0x1003f00fe001f007

def z148 : W := mkw 0x2000aa4400000000 0x108002a910000000 0x00002c6600000000 0x000000b198000000

def z149 : W := mkw 0x01150001ef780000 0x4004540007bde000 0x00000001fffc0000 0x8800000007fff000

def z150 : W := mkw 0x61b5a66b8c6036ea 0x0186d699ae3180db 0xe3ffffff8c607fff 0xd78ffffffe3181ff

def z151 : W := mkw 0x40a002c020148110 0x0902800b00805204 0x00c00380001c0000 0x0003000e00007000

def z152 : W := mkw 0x2000a2c01006c110 0x0880028b00401b04 0x0000c38000038000 0x0000030e00000e00

def z153 : W := mkw 0xb715fc2bdee37eea 0x22dc57f0af7b8dfb 0xff00fc01ffe3ffef 0xeffc03f007ff8fff

def z154 : W := mkw 0xb715fc2b8c6036ea 0x02dc57f0ae3180db 0xff3ffc7f8c607fff 0xf7fcfff1fe3181ff

def z155 : W := mkw 0x2400ff5410836c00 0x309003fd50420db0 0x0000fffe0003fe20 0x140003fff8000ff8

def z156 : W := mkw 0x000000803016c110 0x0800000200c05b04 0x00000000701f8000 0x0800000001c07e00

def z157 : W := mkw 0xfefefbfcb5ffdbfc 0x1ffbfbeff2d7ff6f 0xffffffffffffffff 0xffffffffffffffff

def z158 : W := mkw 0xd3b00001ea500000 0x034ec00007a94000 0xfff00001fffc001f 0xebffc00007fff000

def z159 : W := mkw 0xffeaff555a836c00 0x33ffabfd556a0db0 0xffffffffff83fe3f 0xfffffffffffe0ff8

def z160 : W := mkw 0xfeeafb5452834800 0x33fbabed514a0d20 0xfcc0c38073838002 0x6bf3030e01ce0e00

def z161 : W := mkw 0xfeeafb5463180000 0x53fbabed518c6000 0xfcc0c380739c0002 0x6bf3030e01ce7000

def z162 : W := mkw 0xf6b0fae0f2d7d9b0 0x2bdac3eb83cb5f66 0xfcf0e3e1f3fff1f7 0xfff3c38f87cfffc7

def z163 : W := mkw 0x9f4f59154f280000 0x527d3d64553ca000 0x1f0f1c1e0f800008 0x207c3c70783e0000

def z164 : W := mkw 0x0000042a000036ea 0x00000010a80000db 0x033f3c7e00007ffd 0x140cfcf1f80001ff

def z165 : W := mkw 0xdbff040bef78264a 0x436ffc102fbde099 0xffff1c1ffffc0e1f 0xebfffc707ffff038

def z166 : W := mkw 0x084c01180528024c 0x042130046014a009 0x000c001800000000 0x0000300060000000

def z167 : W := mkw 0xf6a2fa4400000000 0x13da8be910000000 0xff33fc660000002f 0x63fccff198000000

def z168 : W := mkw 0x0d4c55995fafef4c 0x24353156657ebfbd 0x1cccd399fffffffb 0xbc73334e67ffffff

def z169 : W := mkw 0xffffffff8dedbfee 0x17fffffffe37b6ff 0xffffffff8fffffff 0xfffffffffe3fffff

def z170 : W := mkw 0x2000a6ea1006f7fa 0x0880029ba8401bdf 0x0000fffe0003ffe0 0x140003fff8000fff

def z171 : W := mkw 0xfeeafb5400000000 0x13fbabed50000000 0xfcc0c38000000002 0x63f3030e00000000

def z172 : W := mkw 0x2400f3f81087dbfc 0x0c9003cfe0421f6f 0x0000f3f80003ffe0 0x140003cfe0000fff

def z173 : W := mkw 0xb315ac2bde6276ea 0x22cc56b0af7989db 0xe33f3c7ffc607ffd 0xd78cfcf1fff181ff

def z174 : W := mkw 0xbf48fd115a836c00 0x22fd23f4456a0db0 0xffccff99ff83fe3f 0xffff33fe67fe0ff8

def z175 : W := mkw 0x040055ba0085bfee 0x04100156e80216ff 0x0000fffe0003ffe0 0x140003fff8000fff

def z176 : W := mkw 0x2000a00010024000 0x0080028000400900 0xe000c00070038002 0x4b80030001c00e00

def z177 : W := mkw 0xb700fc015a026400 0x22dc03f005680990 0xff00fc01f000702f 0x63fc03f007c001c0

def z178 : W := mkw 0x0c4c519805ad8b4c 0x043131466016b62d 0x1ccc13980ffc0fd8 0x3073304e603ff03f

def z179 : W := mkw 0x2000a00000000000 0x0080028000000000 0xe000e00000000027 0x4380038000000000

def z180 : W := mkw 0x0010000080400000 0x0000400002010000 0x0030000180600015 0x8000c00006018000

def z181 : W := mkw 0x084c000805280248 0x002130002014a009 0x1ccc10180ffc0ffb 0xbc733040603ff03f

def z182 : W := mkw 0xfbffac01ff7a6400 0x63effeb007fde990 0xffff2c01fffc701f 0xebfffcb007fff1c0

def z183 : W := mkw 0x0000000000000000 0x0000000000000000 0x00003c7e00000020 0x100000f1f8000000

def z184 : W := mkw 0x9f4f51994fad8b4c 0x467d3d46653eb62d 0x1fcfd3980fff8ffb 0xbc7f3f4e603ffe3f

def z185 : W := mkw 0xdbff042b8c6036ea 0x036ffc10ae3180db 0xffff3c7f8c607fff 0xf7fffcf1fe3181ff

def z186 : W := mkw 0x0c5c51b885ed9bec 0x04317146e217b66f 0x1cfcf3f98fffffff 0xbc73f3cfe63fffff

def z187 : W := mkw 0x60a0a2c03016c110 0x0982828b00c05b04 0xe0c0c380701f8002 0x4b83030e01c07e00

def z188 : W := mkw 0x0015002a846012ea 0x00005400aa11804b 0x00000000006001c0 0x0000000000018007

def z189 : W := mkw 0xfffffc2bfffb7eea 0x63fffff0afffedfb 0xfffffc7fffffffff 0xfffffff1ffffffff

def z190 : W := mkw 0x68fca2e0b57ed1b0 0x09a3f28b82d5fb46 0xfcfce3e1fffff1ff 0xfff3f38f87ffffc7

def z191 : W := mkw 0x011504238c6034a2 0x000454108e3180d2 0x033f2c678c60701d 0x800cfcb19e3181c0

def z192 : W := mkw 0x084c008805ad8b4c 0x042130022016b62d 0x1ccc00000fff8fdb 0xac733000003ffe3f

def z193 : W := mkw 0xdaff0000a5780000 0x436bfc000295e000 0xffff0000007c001f 0x63fffc000001f000

def z194 : W := mkw 0x60b0a240a0500000 0x0182c28902814000 0xe0f0e3e1f07c0037 0xdb83c38f87c1f000

def z195 : W := mkw 0x00040088052c834c 0x040010022014b20d 0x00000000007c01c0 0x000000000001f007

def z196 : W := mkw 0xfeeafbdc00858b4c 0x17fbabef7002162d 0xfffffffe00038fff 0x77fffffff8000e3f

def z197 : W := mkw 0xbe4af91400000000 0x12f92be450000000 0xff0ffc1e0000002f 0x63fc3ff078000000

def z198 : W := mkw 0x48ff0000a5780000 0x4123fc000295e000 0x00ff0000007c0010 0x0003fc000001f000

def z199 : W := mkw 0xd3b30423ea5034a2 0x434ecc108fa940d2 0xe3332c67f0007004 0x438cccb19fc001c0

def z200 : W := mkw 0x0c4c55ba05adbfee 0x04313156e816b6ff 0x1cccfffe0ffffffb 0xbc7333fff83fffff

def z201 : W := mkw 0xb600f80052834800 0x22d803e0014a0d20 0xff00fc007383802f 0x6bfc03f001ce0e00

def z202 : W := mkw 0xfefafbf4b056d1b0 0x1bfbebefd2c15b46 0xfcf0e3e1f07ff1f7 0xfff3c38f87c1ffc7

def z203 : W := mkw 0x40b30000a0500000 0x4102cc0002814000 0x0033000000000000 0x0000cc0000000000

def z204 : W := mkw 0x010404895fafef4c 0x24041012257ebfbd 0x00000001ffffffc0 0x8c00000007ffffff

def z205 : W := mkw 0x2400f00010834800 0x009003c000420d20 0xfc00f001ff83fe2f 0xeff003c007fe0ff8

def z206 : W := mkw 0x61b5a66bbc7276fa 0x0986d699aef1c9db 0xe33f3c7ffc607ffd 0xd78cfcf1fff181ff

def z207 : W := mkw 0xffffff7fef7836ea 0x53fffffdffbde0db 0xfffffffffffc7fff 0xfffffffffffff1ff

def z208 : W := mkw 0x2400fb5400000000 0x109003ed50000000 0x0000c38000000000 0x0000030e00000000

def z209 : W := mkw 0x04005c0000812c00 0x20100170000204b0 0x00001c0000000e00 0x0000007000000038

def z210 : W := mkw 0xf3b3aa45ea500000 0x53cecea917a94000 0xe3332c67f0000004 0x438cccb19fc00000

def z211 : W := mkw 0x0d5d5199effd8b4c 0x4435754667bff62d 0x1cccd399ffff8ffb 0xbc73334e67fffe3f

def z212 : W := mkw 0xf2a2aa4400000000 0x13ca8aa910000000 0xe000000000000000 0x4380000000000000

def z213 : W := mkw 0x60a0a2c03016c110 0x0982828b00c05b04 0xe0c0c380707f81f3 0xdf83030e01c1fe07

def z214 : W := mkw 0x2010a2e09046d1b0 0x0880428b82411b46 0x0030e3e18063f1f5 0x9400c38f86018fc7

def z215 : W := mkw 0x0c4c500005a90800 0x003131400016a420 0x1cccd0000fff8e3b 0xac733340003ffe38

def z216 : W := mkw 0xb300ac015a026400 0x22cc02b005680990 0xe3003c01fc007e2d 0xc78c00f007f001f8

def z217 : W := mkw 0xfeeafb5410024000 0x13fbabed50400900 0xfffffffff003f03f 0xffffffffffc00fc0

def z218 : W := mkw 0xdbff0401ef782400 0x436ffc1007bde090 0xffff3c01fffc7e3f 0xeffffcf007fff1f8

def z219 : W := mkw 0x0400500000810800 0x0010014000020420 0x1c0010000f800e08 0x20700040003e0038

def z220 : W := mkw 0xd3b30001ea500000 0x434ecc0007a94000 0xe3330001f0000004 0x438ccc0007c00000

def z221 : W := mkw 0x011504ab8dedbfee 0x04045412ae37b6ff 0x000000018fffffc0 0x8c000000063fffff

def z222 : W := mkw 0x0c4c519805ad8b4c 0x043131466016b62d 0x1cc0c3800fff8fc2 0xac73030e003ffe3f

def z223 : W := mkw 0x0400508000858900 0x0010014200021624 0x1cc0d3800fff8ffb 0xbc73034e003ffe3f

def z224 : W := mkw 0x9f4f5c014fa92c00 0x627d3d70053ea4b0 0x1f0f1c000f800e08 0x207c3c70003e0038

def z225 : W := mkw 0x0004000004200000 0x0000100000108000 0x000c00000c600019 0x8000300000318000

def z226 : W := mkw 0xfffbff77884034a2 0x13ffeffdde2100d2 0xffffffff8000703f 0x73fffffffe0001c0

def z227 : W := mkw 0x01110423884034a2 0x000444108e2100d2 0x0000000180007000 0x00000000060001c0

def z228 : W := mkw 0x00000020000010a0 0x0000000080000042 0x00002060000071e0 0x14000081800001c7

def z229 : W := mkw 0xb710fc21dac37ca0 0x22dc43f0876b0df2 0xff30fc61ffe3ffff 0xfffcc3f187ff8fff

def z230 : W := mkw 0x0000040a0000264a 0x0000001028000099 0x00001c1e00000e00 0x0000007078000038

def z231 : W := mkw 0x0000040000002400 0x0000001000000090 0x00003c0000007e20 0x040000f0000001f8

def z232 : W := mkw 0x0000042a000036ea 0x00000010a80000db 0x00003c7e00007fe0 0x140000f1f80001ff

def z233 : W := mkw 0x001000a0b056d1b0 0x0800400282c15b46 0x00302061f07ff1f5 0x9c00c08187c1ffc7

def z234 : W := mkw 0x40a2024400000000 0x1102880910000000 0x0033006600000000 0x0000cc0198000000

def z235 : W := mkw 0x41b506ebac74b7fa 0x0906d41baeb1d2df 0x03ff3fff8c7c7ffd 0x940ffcfffe31f1ff

def z236 : W := mkw 0x41b50001ac700000 0x0106d40006b1c000 0xe3ff0001fc7c001f 0xcb8ffc0007f1f000

def z237 : W := mkw 0xdbea00016b180000 0x436fa80005ac6000 0xffc00001ff9c000f 0xebff000007fe7000

def z238 : W := mkw 0xdfff5c01eff92c00 0x637ffd7007bfe4b0 0xffff1c01fffc0e1f 0xebfffc7007fff038

def z239 : W := mkw 0xdbff00a1ff7ed1b0 0x4b6ffc0287fdfb46 0xffff0001fffff1df 0xeffffc0007ffffc7

def z240 : W := mkw 0x2400f80000000000 0x009003e000000000 0x0000fc0000000020 0x000003f000000000

def z241 : W := mkw 0xb200a80052024000 0x22c802a001480900 0xe000000070000000 0x4380000001c00000

def z242 : W := mkw 0x0015000084600000 0x0000540002118000 0x003f000000600010 0x0000fc0000018000

def z243 : W := mkw 0x64a0fb5400000000 0x119283ed50000000 0xe0f0fffe00000037 0x5383c3fff8000000

def z244 : W := mkw 0x01150401fffb6c00 0x6004541007ffedb0 0x00000001fffffe00 0x8c00000007fffff8

def z245 : W := mkw 0x9e4a591400000000 0x1279296450000000 0x1fcfdf9e0000003b 0x307f3f7e78000000

def z246 : W := mkw 0x40b000a0b056d1b0 0x0902c00282c15b46 0xe0f00001f07ff1d7 0xcf83c00007c1ffc7

def z247 : W := mkw 0xdbff002bef7812ea 0x436ffc00afbde04b 0xffff007ffffc01df 0xfbfffc01fffff007

def z248 : W := mkw 0x0848000000000000 0x0021200000000000 0x1ccc00000000001b 0x2073300000000000

def z249 : W := mkw 0x60b4a2e8b476d3f8 0x0982d28ba2d1db4f 0xe0fcf3f9fc7fffff 0xdf83f3cfe7f1ffff

def z250 : W := mkw 0xf3b3ae67884034a2 0x13ceceb99e2100d2 0xe3332c6780007004 0x438cccb19e0001c0

def z251 : W := mkw 0x0d5d553b8de93eee 0x04357554ee37a4fb 0x1f3f3c7f8fe07ffd 0xb47cfcf1fe3f81ff

def z252 : W := mkw 0x0015002a846012ea 0x00005400aa11804b 0x003f107e0c600ff9 0x9400fc41f831803f

def z253 : W := mkw 0x2115a42b9c6276ea 0x00845690ae7189db 0xe33ffc7ffc63ffff 0xdf8cfff1fff18fff

def z254 : W := mkw 0x0100040108002400 0x0004001004200090 0x03002c0180007004 0x000c00b0060001c0

def z255 : W := mkw 0xdaea000063180000 0x436ba800018c6000 0xffff0000739c001f 0x6bfffc0001ce7000

def z256 : W := mkw 0x93000c014a002400 0x224c003005280090 0x03000c0000000000 0x000c003000000000

def z257 : W := mkw 0xfaeaab5400000000 0x13ebaaad50000000 0xe3ff2ffe00000014 0x538ffcbff8000000

def z258 : W := mkw 0xfbffa241ef780000 0x43effe8907bde000 0xffffe3e1fffc003f 0xfbffff8f87fff000

def z259 : W := mkw 0x60b0a2e0b056d1b0 0x0982c28b82c15b46 0x00f0e3e0007ff1f0 0x1403c38f8001ffc7

def z260 : W := mkw 0xdbff0021ef7810a0 0x436ffc0087bde042 0xffff2061fffc71ff 0xfffffc8187fff1c7

def z261 : W := mkw 0xfbffaa45ef780000 0x53effea917bde000 0xffff2c67fffc001f 0xebfffcb19ffff000

def z262 : W := mkw 0xdeea5190639d8904 0x477ba946418e7624 0xfcc0c380739f8002 0x6bf3030e01ce7e00

def z263 : W := mkw 0xb711fc23dac37ca2 0x22dc47f08f6b0df2 0xff33fc67ff83fe2f 0xeffccff19ffe0ff8

def z264 : W := mkw 0xfeeefb5405280000 0x13fbbbed5014a000 0xfffffffe0ffc003f 0xfbfffffff83ff000

def z265 : W := mkw 0x2c4cfd9815afef4c 0x24b133f66056bfbd 0x1cccff980ffffffb 0xbc7333fe603fffff

def z266 : W := mkw 0x0c4c519805ad8b4c 0x043131466016b62d 0x1cccd3980f9f8e0a 0x2873334e603e7e38

def z267 : W := mkw 0xdbff042bef7836ea 0x436ffc10afbde0db 0xffff0001fffc7fdf 0xeffffc0007fff1ff

def z268 : W := mkw 0x41b50001ef780000 0x4106d40007bde000 0xe0f00001fffc0017 0xcb83c00007fff000

def z269 : W := mkw 0x9600580042810800 0x22580160010a0420 0x1c00000003800000 0x20700000000e0000

def z270 : W := mkw 0xffefff5f0c20264a 0x13ffbffd7c308099 0xfffffffe0c000e3f 0x73fffffff8300038

def z271 : W := mkw 0x0000042a000036ea 0x00000010a80000db 0x0000000000007fc0 0x04000000000001ff

def z272 : W := mkw 0x0000008000048100 0x0000000200001204 0x0000c380000381e0 0x1400030e00000e07

def z273 : W := mkw 0xf3a2ae455a026400 0x33ce8ab915680990 0xe3332c67f0007004 0x438cccb19fc001c0

def z274 : W := mkw 0x0400500000810800 0x0010014000020420 0x1c00c00003838002 0x28700300000e0e00

def z275 : W := mkw 0x0000000000000000 0x0000000000000000 0x003f007e00000010 0x1000fc01f8000000

def z276 : W := mkw 0x2500fc0118836c00 0x209403f004620db0 0x0300fc018c03fe2d 0x840c03f006300ff8

def z277 : W := mkw 0x64b0fbf4b056d1b0 0x1992c3efd2c15b46 0xe0f0fffff07ff1f7 0xdf83c3ffffc1ffc7

def z278 : W := mkw 0x0004000804200248 0x0000100020108009 0x033f3c7e0c600ffd 0x940cfcf1f831803f

def z279 : W := mkw 0x011500a1ff7ed1b0 0x4804540287fdfb46 0x00000001fffff1c0 0x8c00000007ffffc7

def z280 : W := mkw 0x0115040b8c60264a 0x000454102e318099 0x033f1c1f8c600e1d 0x800cfc707e318038

def z281 : W := mkw 0x2515ff7f8c6036ea 0x109457fdfe3180db 0x033fffff8c607ffd 0x940cfffffe3181ff

def z282 : W := mkw 0x93150001ce600000 0x024c540007398000 0xff3f0001ffe0001f 0xebfcfc0007ff8000

def z283 : W := mkw 0x011504018c602400 0x0004541006318090 0x033f3c018c607e3d 0x840cfcf0063181f8

def z284 : W := mkw 0xb700ff555a836c00 0x32dc03fd556a0db0 0xff00ffffff83fe2f 0xfffc03fffffe0ff8

def z285 : W := mkw 0xb300ac015a026400 0x22cc02b005680990 0xe300ec01f003f027 0xcf8c03b007c00fc0

def z286 : W := mkw 0x9f4a5d154a812c00 0x327d2974552a04b0 0x1f0f1c1e0f800e08 0x207c3c70783e0038

def z287 : W := mkw 0x00100020804010a0 0x0000400082010042 0x00000001806071c0 0x84000000060181c7

def z288 : W := mkw 0x0000040010836c00 0x2000001000420db0 0x000000000003fe00 0x0400000000000ff8

def z289 : W := mkw 0x0404500804a10a48 0x0010114020128429 0x1c0cd0180fe38ffb 0xbc703340603f8e3f

def z290 : W := mkw 0x60b0a2e0b056d1b0 0x0982c28b82c15b46 0xe3fffffff07ff1ff 0xdf8fffffffc1ffc7

def z291 : W := mkw 0x60a0a2c03016c110 0x0982828b00c05b04 0xe0f0e3e0701f8037 0x5b83c38f81c07e00

def z292 : W := mkw 0xfeeafb5400000000 0x13fbabed50000000 0xfff3efe600000006 0x63ffcfbf98000000

def z293 : W := mkw 0xf2a2aa4400000000 0x13ca8aa910000000 0xe33f3c7e0000003d 0x538cfcf1f8000000

def z294 : W := mkw 0x0c485190018d8904 0x0431214640063624 0x1cc0c380039f8002 0x2873030e000e7e00

def z295 : W := mkw 0x48ea035400000000 0x1123a80d50000000 0x03ff3ffe0000003d 0x100ffcfff8000000

def z296 : W := mkw 0x050054015a836c00 0x20140150056a0db0 0x1c00d001ff83fe2b 0xac70034007fe0ff8

def z297 : W := mkw 0x0010042a804036ea 0x00004010aa0100db 0x00303c7f80607ff5 0x9400c0f1fe0181ff

def z298 : W := mkw 0x2010a0a0b056d1b0 0x0880428282c15b46 0xe000e001f07ff1e7 0xcf80038007c1ffc7

def z299 : W := mkw 0x0115042bef7836ea 0x40045410afbde0db 0x00000001fffc7fc0 0x8c00000007fff1ff

def z300 : W := mkw 0x61b5a6ebbc76f7fa 0x0986d69baef1dbdf 0xe0f0e3e1fc7ffff7 0xdf83c38f87f1ffff

def z301 : W := mkw 0xd3b70001ef780000 0x434edc0007bde000 0xe3330001fffc0004 0xcb8ccc0007fff000

def z302 : W := mkw 0x60b0a260b05250b0 0x0982c28982c14942 0xe0f0e3e1f0007037 0x5383c38f87c001c0

def z303 : W := mkw 0xfeeafbd4018d8904 0x17fbabef50063624 0xfffffffe039f803f 0x7bfffffff80e7e00

def z304 : W := mkw 0x9200000000000000 0x0248000000000000 0xff0000000000000f 0x63fc000000000000

def z305 : W := mkw 0x40b002e0a05491b0 0x0902c00b82815246 0xe0f003e1f07c01d7 0xdb83c00f87c1f007

def z306 : W := mkw 0x01150001ef780000 0x4004540007bde000 0x033f0001fffc001d 0x880cfc0007fff000

def z307 : W := mkw 0x0000000800000248 0x0000000020000009 0x0000101800000fe0 0x140000406000003f

def z308 : W := mkw 0x9b4f00014f280000 0x426d3c00053ca000 0x1fcf00000ffc001b 0xa87f3c00003ff000

def z309 : W := mkw 0x0100040108002400 0x0004001004200090 0x033f3c7f8c007e3d 0x940cfcf1fe3001f8

def z310 : W := mkw 0xf6a0fa4000000000 0x03da83e900000000 0xfff0ffe00000003f 0x73ffc3ff80000000

def z311 : W := mkw 0x0115042b8c6036ea 0x00045410ae3180db 0x033f00018c607fdd 0x840cfc00063181ff

def z312 : W := mkw 0x97055c0b4ea12e4a 0x225c15702d3a84b9 0x1f0f1c1e0f800e08 0x207c3c70783e0038

def z313 : W := mkw 0x0000000000000000 0x0000000000000000 0x1c0000000f80000b 0xa8700000003e0000

def z314 : W := mkw 0x0105042b0c2036ea 0x00041410ac3080db 0x030f3c7e0c007fe8 0x140c3cf1f83001ff

def z315 : W := mkw 0x9e4a591400000000 0x1279296450000000 0x1f0f1c1e00000008 0x207c3c7078000000

def z316 : W := mkw 0xbf48fd915b8fed04 0x26fd23f6456e3fb4 0xffc0ff81ff9ffe2f 0xefff03fe07fe7ff8

def z317 : W := mkw 0xdaea000000000000 0x036ba80000000000 0xfcc0000000000002 0x63f3000000000000

def z318 : W := mkw 0x2c48fb5400000000 0x10b123ed50000000 0x1cccfffe0000003b 0x307333fff8000000

def z319 : W := mkw 0x9315042bce6036ea 0x024c5410af3980db 0xff3f3c7fffe07fff 0xfffcfcf1ffff81ff

def z320 : W := mkw 0x08480190010c8104 0x0421200640043204 0x00c00380001c0000 0x0003000e00007000

def z321 : W := mkw 0x0848000001080000 0x0021200000042000 0x1cc00000039c0002 0x28730000000e7000

def z322 : W := mkw 0xd2a2000062100000 0x434a880001884000 0xe000000070000000 0x4380000001c00000

def z323 : W := mkw 0x0c4c511804200248 0x0031314460108009 0x1cccd3980c600ffb 0xb473334e6031803f

def z324 : W := mkw 0xffeaff555a836c00 0x33ffabfd556a0db0 0xffc0ff81ff83fe2f 0xefff03fe07fe0ff8

def z325 : W := mkw 0x000000a01006d1b0 0x0800000280401b46 0x000000000003f1c0 0x0400000000000fc7

def z326 : W := mkw 0x64b0fee0b0d7fdb0 0x2992c3fb82c35ff6 0xe0f0ffe1f07ffff7 0xdf83c3ff87c1ffff

def z327 : W := mkw 0x48ff002aa57812ea 0x4123fc00aa95e04b 0x00ff007e007c01d0 0x1003fc01f801f007

def z328 : W := mkw 0x2c4cfbdc05ad8b4c 0x14b133ef7016b62d 0x1cccfffe0fff8ffb 0xbc7333fff83ffe3f

def z329 : W := mkw 0x48ea035400000000 0x1123a80d50000000 0x00c0038000000000 0x0003000e00000000

def z330 : W := mkw 0xfeeafb5452834800 0x33fbabed514a0d20 0xfffffffe7383803f 0x7bfffffff9ce0e00

def z331 : W := mkw 0xfeeafb5463180000 0x53fbabed518c6000 0xfffffffe739c003f 0x7bfffffff9ce7000

def z332 : W := mkw 0x0c48511000000000 0x0031214440000000 0x1c0c101800000008 0x2070304060000000

def z333 : W := mkw 0x9f4f51194fa90a4c 0x467d3d44653ea429 0x1f0f10180f800e08 0x207c3c40603e0038

def z334 : W := mkw 0x0c48511000810800 0x0031214440020420 0x1cccd3980f838e3b 0xbc73334e603e0e38

def z335 : W := mkw 0x0d4c55990dadaf4c 0x043531566436b6bd 0x1fccff998fffffff 0xbc7f33fe663fffff

def z336 : W := mkw 0x2000a260100250b0 0x0880028980400942 0x0000206000007000 0x00000081800001c0

def z337 : W := mkw 0x2400fc0010836c00 0x209003f000420db0 0x1c00fc000f83fe2b 0xac7003f0003e0ff8

def z338 : W := mkw 0x0c48519000048100 0x0031214640001204 0x1cccd398007f81fb 0xbc73334e6001fe07

def z339 : W := mkw 0xfafaa2e0b056d1b0 0x0bebea8b82c15b46 0xffffe3e1f07ff1ff 0xffffff8f87c1ffc7

def z340 : W := mkw 0x2000a00010024000 0x0080028000400900 0xe0002001f0007004 0x4380008007c001c0

def z341 : W := mkw 0x0004042a042036ea 0x00001010a81080db 0x000c3c7e0c607ff9 0x940030f1f83181ff

def z342 : W := mkw 0x0000008000048100 0x0000000200001204 0x00000000007f81c0 0x8c0000000001fe07

def z343 : W := mkw 0xb700fc0108002400 0x02dc03f004200090 0xff00fc018c007e2f 0xe7fc03f0063001f8

def z344 : W := mkw 0xfeeafb5400810800 0x13fbabed50020420 0xfffffffe0f838e3f 0xfffffffff83e0e38

def z345 : W := mkw 0xfeeaf80000000000 0x03fbabe000000000 0xfffffc000000003f 0x63fffff000000000

def z346 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000200180007025 0x84000080060001c0

def z347 : W := mkw 0x48ea000021180000 0x4123a80000846000 0x00c00000001c0000 0x0003000000007000

def z348 : W := mkw 0xfffcfff9fffffffc 0x2ffff3ffe7ffffff 0xfffcfff9ffffffff 0xfffff3ffe7ffffff

def z349 : W := mkw 0x48ff0198a57c834c 0x4523fc066295f20d 0x00ff0398007c01d0 0x1003fc0e6001f007

def z350 : W := mkw 0xfefffb54a5780000 0x53fbffed5295e000 0xfffffffe007c003f 0x73fffffff801f000

def z351 : W := mkw 0xdbfb0001eb580000 0x436fec0007ad6000 0xfff30001f39c0006 0x6bffcc0007ce7000

def z352 : W := mkw 0x0000008000048100 0x0000000200001204 0x00c0c380001f8002 0x0803030e00007e00

def z353 : W := mkw 0x60b0a2e0b056d1b0 0x0982c28b82c15b46 0xe0302061f07ff1c4 0xcf80c08187c1ffc7

def z354 : W := mkw 0xfaeaa2c0731ec110 0x4bebaa8b01cc7b04 0xfcc0c380739f8002 0x6bf3030e01ce7e00

def z355 : W := mkw 0x60b0a000b0524000 0x0182c28002c14900 0xe0f0e001f07ff037 0xcf83c38007c1ffc0

def z356 : W := mkw 0xfeeafb5400000000 0x13fbabed50000000 0xffc0ff800000002f 0x63ff03fe00000000

def z357 : W := mkw 0x0404508805ad8b4c 0x041011422016b62d 0x1c00d0000fff8feb 0xac700340003ffe3f

def z358 : W := mkw 0x0c48511001890804 0x0431214440062420 0x1c00000003800000 0x20700000000e0000

def z359 : W := mkw 0x930004014a002400 0x024c001005280090 0xff003c01ff807e2f 0xeffc00f007fe01f8

def z360 : W := mkw 0xfffff801fffb4800 0x63ffffe007ffed20 0xffffc001ffff801f 0xebffff0007fffe00

def z361 : W := mkw 0x0115042bef7836ea 0x40045410afbde0db 0x033f3c7ffffc7ffd 0x9c0cfcf1fffff1ff

def z362 : W := mkw 0x0d4d551b0da92e4e 0x043535546c36a4b9 0x1f0f1c1e0f800e08 0x207c3c70783e0038

def z363 : W := mkw 0xb600f80000810800 0x02d803e000020420 0xff00fc000f838e2f 0xeffc03f0003e0e38

def z364 : W := mkw 0x0000008000048100 0x0000000200001204 0x00c00380007c01d0 0x1003000e0001f007

def z365 : W := mkw 0xb700fee15a87fdb0 0x2adc03fb856a1ff6 0xff00ffe1ff83ffef 0xfffc03ff87fe0fff

def z366 : W := mkw 0x0101040308002402 0x000404100c200090 0x03030c0600000000 0x000c0c3018000000

def z367 : W := mkw 0xb600f80000000000 0x02d803e000000000 0xfc00c00000000002 0x63f0030000000000

def z368 : W := mkw 0x0115042b8c6036ea 0x00045410ae3180db 0x033f2c7f806071d4 0x100cfcb1fe0181c7

def z369 : W := mkw 0x4cff5198a5fd8b4c 0x4533fd466297f62d 0x1cffd3980fff8ffb 0xbc73ff4e603ffe3f

def z370 : W := mkw 0x60a0a24010024000 0x0182828900400900 0xe0f0e3e1f003f037 0xdf83c38f87c00fc0

def z371 : W := mkw 0x0c4c511805a90a4c 0x043131446016a429 0x1c0c10180fe00ff9 0xb4703040603f803f

def z372 : W := mkw 0x0115042b8c6036ea 0x00045410ae3180db 0x030f1c1f8c607fc8 0x840c3c707e3181ff

def z373 : W := mkw 0x48ea000000000000 0x0123a80000000000 0x00ff000000000010 0x0003fc0000000000

def z374 : W := mkw 0x48ee03dc052c834c 0x1523b80f7014b20d 0x00ff03fe007c01d0 0x1003fc0ff801f007

def z375 : W := mkw 0xdbff0001ef780000 0x436ffc0007bde000 0xffff3c7ffffc003f 0xfbfffcf1fffff000

def z376 : W := mkw 0x0c48519800858b4c 0x043121466002162d 0x1cccd39800038ffb 0x3473334e60000e3f

def z377 : W := mkw 0x40b00260a05010b0 0x0902c00982814042 0x0030006000000000 0x0000c00180000000

def z378 : W := mkw 0xfefafb54a0500000 0x13fbebed52814000 0xfffffffff07c003f 0xfbffffffffc1f000

def z379 : W := mkw 0xb700fc015a836c00 0x22dc03f0056a0db0 0xfc00c001ff83fe02 0xeff0030007fe0ff8

def z380 : W := mkw 0x9e4e591c05a90a4c 0x167939647016a429 0x1f0f1c1e0f800e08 0x207c3c70783e0038

def z381 : W := mkw 0x4cea535400000000 0x1133a94d50000000 0x1cffd3fe0000003b 0x3073ff4ff8000000

def z382 : W := mkw 0x084c0198052c834c 0x042130066014b20d 0x00ccc398007f81f3 0x9c03330e6001fe07

def z383 : W := mkw 0x0005000a0420024a 0x0000140028108009 0x000f001e00000000 0x00003c0078000000

def z384 : W := mkw 0x49ff077f8c6036ea 0x1127fc1dfe3180db 0x03ff3fff8c607ffd 0x940ffcfffe3181ff

def z385 : W := mkw 0x2400f80010834800 0x209003e000420d20 0x0000c00000038000 0x0000030000000e00

def z386 : W := mkw 0x9f5f5d3f8c6036ea 0x127d7d74fe3180db 0x1f3f3c7f8c607ffd 0xb47cfcf1fe3181ff

def z387 : W := mkw 0x4cee53dc05ad8b4c 0x1533b94f7016b62d 0x1cffd3fe0fff8ffb 0xbc73ff4ff83ffe3f

def z388 : W := mkw 0x0004000804200248 0x0000100020108009 0x000c0018006001d0 0x1000300060018007

def z389 : W := mkw 0x0c48511000000000 0x0031214440000000 0x1ffffffe0000003f 0x307ffffff8000000

def z390 : W := mkw 0xf3b0aee1fa56f5b0 0x2bcec2bb87e95bd6 0xe3f0efe1f07ff1f7 0xdf8fc3bf87c1ffc7

def z391 : W := mkw 0xdbff02e1ef7c91b0 0x4b6ffc0b87bdf246 0xffff03e1fffc01df 0xfbfffc0f87fff007

def z392 : W := mkw 0x000002e0000491b0 0x0800000b80001246 0x000003e0000001c0 0x1000000f80000007

def z393 : W := mkw 0x001000a0804491a0 0x0000400282011246 0x00f0e3e1807ff1f7 0x9c03c38f8601ffc7

def z394 : W := mkw 0x9a4a000043080000 0x42692800010c2000 0x1c00000003800000 0x20700000000e0000

def z395 : W := mkw 0x0105040b0c20264a 0x000414102c308099 0x000000000c000e00 0x0000000000300038

def z396 : W := mkw 0xbe4cf99857afcb4c 0x26f933e6615ebf2d 0xfcccd3987fff8ffb 0xfff3334e61fffe3f

def z397 : W := mkw 0x051555bb8ce5bfee 0x04145556ee3396ff 0x033fffff8c63fffd 0x940cfffffe318fff

def z398 : W := mkw 0x49ff042bad7836ea 0x4127fc10aeb5e0db 0x03ff3c7f8c7c7ffd 0x940ffcf1fe31f1ff

def z399 : W := mkw 0x0115042b8c6036ea 0x00045410ae3180db 0x000c10198c607ff9 0x94003040663181ff

def z400 : W := mkw 0x6cecf3d805ad8b4c 0x05b3b3cf6016b62d 0xfcfcf3f80fff8fff 0xfff3f3cfe03ffe3f

def z401 : W := mkw 0x6dfdf7fbbdfffffe 0x0db7f7dfeef7ffff 0xffffffffffffffff 0xffffffffffffffff

def z402 : W := mkw 0xdbff00018c600000 0x036ffc0006318000 0xffff00018c60001f 0xe3fffc0006318000

def z403 : W := mkw 0x010004014a812c00 0x20040010052a04b0 0x000000000f800e00 0x00000000003e0038

def z404 : W := mkw 0xffffff7fdee37eea 0x33fffffdff7b8dfb 0xffffffffffe3ffff 0xffffffffffff8fff

def z405 : W := mkw 0x0400511000000000 0x0010014440000000 0x0000d39800000020 0x1000034e60000000

def z406 : W := mkw 0x930000014a000000 0x024c000005280000 0x1f0000000f800008 0x207c0000003e0000

def z407 : W := mkw 0xbf4cfd195fab6e4c 0x26fd33f4657eadb9 0xff0cfc19ff83fe2f 0xeffc33f067fe0ff8

def z408 : W := mkw 0xf7b5feebfef7fffa 0x2bded7fbaffbdfff 0xffffffffffffffff 0xffffffffffffffff

def z409 : W := mkw 0x011500018c600000 0x0004540006318000 0x000000018c600000 0x8000000006318000

def z410 : W := mkw 0x40b00020a05010a0 0x0102c00082814042 0xe0f02061f07c71f7 0xdf83c08187c1f1c7

def z411 : W := mkw 0xdbff0001ef780000 0x436ffc0007bde000 0xe3ff0001f07c0014 0x438ffc0007c1f000

def z412 : W := mkw 0x64b0f3f8b0d7dbfc 0x0d92c3cfe2c35f6f 0xe0f0f3f9f07ffff7 0xdf83c3cfe7c1ffff

def z413 : W := mkw 0x01110423884034a2 0x000444108e2100d2 0x03332c67806071f5 0x940cccb19e0181c7

def z414 : W := mkw 0xfefafb74b05250b0 0x1bfbebedd2c14942 0xfffffffff000703f 0x73ffffffffc001c0

def z415 : W := mkw 0xffeffb554f280000 0x53ffbfed553ca000 0xfffffffe0f80003f 0x73fffffff83e0000

def z416 : W := mkw 0x0115042b8c6036ea 0x00045410ae3180db 0x03332c678c607fc4 0x840cccb19e3181ff

def z417 : W := mkw 0x0105040b0c20264a 0x000414102c308099 0x030f3c1f8c007e2d 0x840c3cf07e3001f8

def z418 : W := mkw 0x010404090c202648 0x0004101024308099 0x030c3c198c607ffd 0x940c30f0663181ff

def z419 : W := mkw 0x010004015a026400 0x2004001005680990 0x00000001f0007000 0x0000000007c001c0

def z420 : W := mkw 0xdaea035400000000 0x136ba80d50000000 0xffff03fe0000001f 0x73fffc0ff8000000

def z421 : W := mkw 0xb715fc01fffb6c00 0x62dc57f007ffedb0 0xff00fc01fffffe2f 0xeffc03f007fffff8

def z422 : W := mkw 0x0c4c519805ad8b4c 0x043131466016b62d 0x1cccc39803ff81d2 0x3873330e600ffe07

def z423 : W := mkw 0x930000014a000000 0x024c000005280000 0xe3000001f0000004 0x438c000007c00000

def z424 : W := mkw 0x48ff02e0a57c91b0 0x4923fc0b8295f246 0x00ff03e0007c01d0 0x1003fc0f8001f007

def z425 : W := mkw 0x60a0a24000000000 0x0182828900000000 0xe030206000000004 0x4380c08180000000

def z426 : W := mkw 0xb300a0015a024000 0x02cc028005680900 0xff00e001ff83f02f 0xeffc038007fe0fc0

def z427 : W := mkw 0x0004008805ad8b4c 0x040010022016b62d 0x00c0c3800fff8ff3 0x9c03030e003ffe3f

def z428 : W := mkw 0x000001980004834c 0x040000066000120d 0x00000398000001c0 0x1000000e60000007

def z429 : W := mkw 0x2000a2e01006d1b0 0x0880028b80401b46 0x00c0e3e0007ff1f3 0x9c03038f8001ffc7

def z430 : W := mkw 0x00000080018d8904 0x0400000200063624 0x00000000039f8000 0x08000000000e7e00

def z431 : W := mkw 0xfeeafb5400000000 0x13fbabed50000000 0xffffc3800000001f 0x63ffff0e00000000

def z432 : W := mkw 0x0c4c511805a90a4c 0x043131446016a429 0x1c0cd0180f838e2b 0xac703340603e0e38

def z433 : W := mkw 0x9e4a591400000000 0x1279296450000000 0x1c00000000000000 0x2070000000000000

def z434 : W := mkw 0x9b4f040b4f28264a 0x426d3c102d3ca099 0x1f0f1c1e0f800e08 0x207c3c70783e0038

def z435 : W := mkw 0x0015002a846012ea 0x00005400aa11804b 0x003f207f806071f5 0x9400fc81fe0181c7

def z436 : W := mkw 0x68ffa2e0b57ed1b0 0x49a3fe8b82d5fb46 0xe0ffe3e1f07ff1f7 0xdf83ff8f87c1ffc7

def z437 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000006001f1 0x9400000000018007

def z438 : W := mkw 0xffeafc017b9b6c00 0x63ffabf005ee6db0 0xffc0fc01ff9ffe2f 0xefff03f007fe7ff8

def z439 : W := mkw 0x095d042b8d6836ea 0x00257410ae35a0db 0x1fff3c7f8ffc7fff 0xbc7ffcf1fe3ff1ff

def z440 : W := mkw 0xd3b7042bee7036ea 0x434edc10afb9c0db 0xe33f3c7ffc607ffd 0xd78cfcf1fff181ff

def z441 : W := mkw 0x2515fc2b9ce37eea 0x209457f0ae738dfb 0x033ffc7f8c63fffd 0x940cfff1fe318fff

def z442 : W := mkw 0x61b5a2e1bc76d1b0 0x0986d68b86f1db46 0xe3ffe3e1fc7ff1ff 0xdf8fff8f87f1ffc7

def z443 : W := mkw 0x0400519800858b4c 0x041001466002162d 0x1c00d3980f838feb 0xbc70034e603e0e3f

def z444 : W := mkw 0xffeafb554a000000 0x13ffabed55280000 0xffffffffff80003f 0xfbfffffffffe0000

def z445 : W := mkw 0x61b0a6e1b856f5b0 0x0986c29b86e15bd6 0xe3f0ffe1fc7fffff 0xdf8fc3ff87f1ffff

def z446 : W := mkw 0x0000000063180000 0x40000000018c6000 0x00000000739c0000 0x0800000001ce7000

def z447 : W := mkw 0xdbff0001ef780000 0x436ffc0007bde000 0xff3f0001ff80000c 0x63fcfc0007fe0000

def z448 : W := mkw 0x0000000000000000 0x0000000000000000 0x00c0c38000000033 0x1003030e00000000

def z449 : W := mkw 0xffeaff554a812c00 0x33ffabfd552a04b0 0xfffffffe0f800e3f 0x73fffffff83e0038

def z450 : W := mkw 0x0115042b8c6036ea 0x00045410ae3180db 0x003020618c607ff5 0x9400c081863181ff

def z451 : W := mkw 0xdbea00014a000000 0x036fa80005280000 0xffff0001ff80001f 0xebfffc0007fe0000

def z452 : W := mkw 0xdbef00016f380000 0x436fbc0005bce000 0xffcf00007f9c000a 0x6bff3c0001fe7000

def z453 : W := mkw 0x6ce8f3d0319fc914 0x0db3a3cf40c67f24 0xfcc0c380739f8002 0x6bf3030e01ce7e00

def z454 : W := mkw 0x0d4d559b0dadaf4e 0x043535566c36b6bd 0x1fcfdf9e0fff8ffb 0xbc7f3f7e783ffe3f

def z455 : W := mkw 0x0000000000000000 0x0000000000000000 0x03003c000000002d 0x000c00f000000000

def z456 : W := mkw 0x68eaa35400000000 0x11a3aa8d50000000 0xe0ffe3fe00000037 0x5383ff8ff8000000

def z457 : W := mkw 0xbe4afb5400000000 0x12f92bed50000000 0x1f0ffffe00000028 0x307c3ffff8000000

def z458 : W := mkw 0xfffffb558c600000 0x13ffffed56318000 0xffffffff8c60003f 0xf3fffffffe318000

def z459 : W := mkw 0x010004015a836c00 0x20040010056a0db0 0x03003c01ff83fe2d 0x8c0c00f007fe0ff8

def z460 : W := mkw 0xfffff801ef780000 0x43ffffe007bde000 0xfffffc01fffc003f 0xebfffff007fff000

def z461 : W := mkw 0x64b0f2e0b0d7d9b0 0x0992c3cb82c35f66 0xfcf0f3e1ffffffff 0xfff3c3cf87ffffff

def z462 : W := mkw 0x2c4cf3f815afdbfc 0x0cb133cfe056bf6f 0x1cccf3f80ffffffb 0xbc7333cfe03fffff

def z463 : W := mkw 0x60b0a2e0b056d1b0 0x0982c28b82c15b46 0xe0f0c3e0707f81d2 0x5b83c30f81c1fe07

def z464 : W := mkw 0xfeeafbd400048100 0x13fbabef50001204 0xfffffffe007f81ff 0xfffffffff801fe07

def z465 : W := mkw 0x9b4c00014f280000 0x026d3000053ca000 0xffcc0001fffc001f 0xebff300007fff000

def z466 : W := mkw 0x2c4cf19815afcb4c 0x04b133c66056bf2d 0xfcccf399ffffffff 0xfff333ce67ffffff

def z467 : W := mkw 0x60b0a2e0a05491b0 0x0982c28b82815246 0xe0f0e3e0007c01f7 0x5383c38f8001f007

def z468 : W := mkw 0x0100040108002400 0x0004001004200090 0x000000018c007e00 0x84000000063001f8

def z469 : W := mkw 0xb700fc015a836c00 0x22dc03f0056a0db0 0xff00dc007f838e0a 0x6bfc037001fe0e38

def z470 : W := mkw 0xb700fc015a836c00 0x22dc03f0056a0db0 0xff003c01ff807e0c 0x63fc00f007fe01f8

def z471 : W := mkw 0xffeeffdd5fafef4c 0x37ffbbff757ebfbd 0xffffffffffffffff 0xffffffffffffffff

def z472 : W := mkw 0xfffffbddeffd8b4c 0x57ffffef77bff62d 0xffffffffffff8fff 0xfffffffffffffe3f

def z473 : W := mkw 0xd2a2000000000000 0x034a880000000000 0xe333000000000004 0x438ccc0000000000

def z474 : W := mkw 0xfefafbf4a05491b0 0x1bfbebefd2815246 0xfffffffe007c01ff 0x73fffffff801f007

def z475 : W := mkw 0x084c0198052c834c 0x042130066014b20d 0x1ccc03980ffc01db 0xb873300e603ff007

def z476 : W := mkw 0x0c48511000000000 0x0031214440000000 0x1cc0c38000000002 0x2073030e00000000

def z477 : W := mkw 0xdbff0199ef7c834c 0x476ffc0667bdf20d 0xffff0399fffc01df 0xfbfffc0e67fff007

def z478 : W := mkw 0x68faa3f4b056d1b0 0x19a3ea8fd2c15b46 0xe0ffe3fff07ff1f7 0xdf83ff8fffc1ffc7

def z479 : W := mkw 0xfffffd99ffffef4c 0x67fffff667ffffbd 0xffffff99ffffffff 0xfffffffe67ffffff

def z480 : W := mkw 0x011504ab8dedbfee 0x04045412ae37b6ff 0x033f3c7f8ffffffd 0x9c0cfcf1fe3fffff

def z481 : W := mkw 0x001000a0a05491b0 0x0800400282815246 0x00000000007c01c0 0x000000000001f007

def z482 : W := mkw 0x48ff037e846012ea 0x1123fc0dfa11804b 0x00ff03fe006001d0 0x1003fc0ff8018007

def z483 : W := mkw 0x2000a2e01006d1b0 0x0880028b80401b46 0xe000e3e1f003f1e7 0xdf80038f87c00fc7

def z484 : W := mkw 0x0c4c511005280000 0x003131444014a000 0x1cccd3980ffc003b 0xb873334e603ff000

def z485 : W := mkw 0x60b0a260b05250b0 0x0982c28982c14942 0xe0f02061f07c7017 0xcb83c08187c1f1c0

def z486 : W := mkw 0x0004008804248348 0x000010022010920d 0x00ccd3980c7f8ffb 0x9c03334e6031fe3f

def z487 : W := mkw 0x011504abbc76f7fa 0x08045412aef1dbdf 0x00000001fc7fffc0 0x8c00000007f1ffff

def z488 : W := mkw 0xfbffa6ebff7ef7fa 0x4beffe9baffdfbdf 0xffffffffffffffff 0xffffffffffffffff

def z489 : W := mkw 0x0400511800810a4c 0x0410014460020429 0x0000101800000e00 0x0000004060000038

def z490 : W := mkw 0x0115042b8c6036ea 0x00045410ae3180db 0x00003c7f8c607fe0 0x940000f1fe3181ff

def z491 : W := mkw 0x40a0000020100000 0x0102800000804000 0xe0c00000701c0002 0x4b83000001c07000

def z492 : W := mkw 0x0115042bdee37eea 0x20045410af7b8dfb 0x00000001ffe3ffc0 0x8c00000007ff8fff

def z493 : W := mkw 0xbf4ffc015fab6c00 0x62fd3ff0057eadb0 0xff0ffc01ff83fe2f 0xeffc3ff007fe0ff8

def z494 : W := mkw 0x48ff0354a5780000 0x5123fc0d5295e000 0x00ff03fe007c0010 0x1003fc0ff801f000

def z495 : W := mkw 0x48ff0000a5780000 0x4123fc000295e000 0xe0ff0001f07c0017 0xcb83fc0007c1f000

def z496 : W := mkw 0x0000000000000000 0x0000000000000000 0x00c00000007c0013 0x880300000001f000

def z497 : W := mkw 0xfeeafbf41006d1b0 0x1bfbabefd0401b46 0xfffffffe0003f1ff 0x77fffffff8000fc7

def z498 : W := mkw 0x00100020804010a0 0x0000400082010042 0x0030206180007004 0x0000c081860001c0

def z499 : W := mkw 0x4cfc53f8a5fd9bfc 0x0d33f14fe297f66f 0x1cfcd3f80fff8ffb 0xbc73f34fe03ffe3f

def z500 : W := mkw 0xdbff0355ef780000 0x536ffc0d57bde000 0xffff03fffffc001f 0xfbfffc0ffffff000

def z501 : W := mkw 0x60b5a2eab476d3fa 0x0982d68baad1db4f 0xe0ffe3fff07ff1f7 0xdf83ff8fffc1ffc7

def z502 : W := mkw 0xf6a2fb5400000000 0x13da8bed50000000 0xe333fffe00000024 0x538ccffff8000000

def z503 : W := mkw 0x0c5d51ba85ed9bee 0x04317546ea17b66f 0x1cffd3fe0fff8ffb 0xbc73ff4ff83ffe3f

def z504 : W := mkw 0x0105040b0c20264a 0x000414102c308099 0x030f1c1e0c600ff9 0x940c3c707831803f

def z505 : W := mkw 0xffeaff555a026400 0x33ffabfd55680990 0xfffffffff000703f 0x73ffffffffc001c0

def z506 : W := mkw 0xfffbfb55ea500000 0x53ffefed57a94000 0xfffffffff000003f 0x73ffffffffc00000

def z507 : W := mkw 0x60b0a6eab056f7fa 0x0982c29baac15bdf 0xe0f0fffff07ffff7 0xdf83c3ffffc1ffff

def z508 : W := mkw 0x2000a0801006c100 0x0080028200401b04 0xe0c0e381f07ff1f7 0xdf83038e07c1ffc7

def z509 : W := mkw 0xdfff5191effd8904 0x477ffd4647bff624 0xffffc381ffff801f 0xebffff0e07fffe00

def z510 : W := mkw 0x60b0a2e0b056d1b0 0x0982c28b82c15b46 0xe0c0c381f07ff1c2 0xcf83030e07c1ffc7

def z511 : W := mkw 0xfeeefb5c05a90a4c 0x17fbbbed7016a429 0xfffffffe0f800e3f 0x73fffffff83e0038

def z512 : W := mkw 0x0015042a846036ea 0x00005410aa1180db 0x003f3c7e00607ff0 0x1400fcf1f80181ff

def z513 : W := mkw 0xffeaff5508002400 0x13ffabfd54200090 0xffffffff8c007e3f 0xf7fffffffe3001f8

def z514 : W := mkw 0x0000000000000000 0x0000000000000000 0x033f00000000001d 0x000cfc0000000000

def z515 : W := mkw 0x9f4c5d994fadaf4c 0x267d3176653eb6bd 0x1fccdf980fff8ffb 0xbc7f337e603ffe3f

def z516 : W := mkw 0xffeafc015a836c00 0x23ffabf0056a0db0 0xfffffc01ff83fe3f 0xeffffff007fe0ff8

def z517 : W := mkw 0x0c485190018d8904 0x0431214640063624 0x1cc0c38003ff81f3 0xbc73030e000ffe07

def z518 : W := mkw 0x60a0a2c000048100 0x0182828b00001204 0xe0f0e3e0007f81f7 0xdf83c38f8001fe07

def z519 : W := mkw 0xb704fc095ea36e48 0x22dc13f0257a8db9 0xff0cfc19ffe3ffff 0xfffc33f067ff8fff

def z520 : W := mkw 0x2400fd981087ef4c 0x249003f660421fbd 0x0000ff980003ffe0 0x140003fe60000fff

def z521 : W := mkw 0x9b5f0001ef780000 0x426d7c0007bde000 0x1f0f0001fffc0008 0xa87c3c0007fff000

def z522 : W := mkw 0xbf4afd155a836c00 0x32fd2bf4556a0db0 0xff0ffc1fff83fe2f 0xeffc3ff07ffe0ff8

def z523 : W := mkw 0x2400ff7e000036ea 0x109003fdf80000db 0x0000fffe00007fe0 0x140003fff80001ff

def z524 : W := mkw 0x0c4c511805a90a4c 0x043131446016a429 0x1cccd3980f800e3b 0x3073334e603e0038

def z525 : W := mkw 0x6cecf3d835bfcb5c 0x0db3b3cf60d6ff2d 0xfcccd3987fff8ffb 0xfff3334e61fffe3f

def z526 : W := mkw 0x0c4c5198052c834c 0x043131466014b20d 0x1cccd398007c01fb 0x3073334e6001f007

def z527 : W := mkw 0xf6a0fac07297c910 0x2bda83eb01ca5f24 0xfcc0c380739f8002 0x6bf3030e01ce7e00

def z528 : W := mkw 0xb600fc0010836c00 0x22d803f000420db0 0xff00fc000003fe2f 0x67fc03f000000ff8

def z529 : W := mkw 0x0c485190018d8904 0x0431214640063624 0x1cccd398039f803b 0x3873334e600e7e00

def z530 : W := mkw 0x0004000805a90a4c 0x040010002016a429 0x000000000f800e00 0x00000000003e0038

def z531 : W := mkw 0xbf5dfdbbdfefffee 0x26fd77f6ef7fbfff 0xffffffffffffffff 0xffffffffffffffff

def z532 : W := mkw 0x60a0a2c03016c110 0x0982828b00c05b04 0xe0c0e381f01ff027 0xcf83038e07c07fc0

def z533 : W := mkw 0xdafa0000a0500000 0x036be80002814000 0xffff0001f07c001f 0xebfffc0007c1f000

def z534 : W := mkw 0xfeeafb5400000000 0x13fbabed50000000 0xfcf0e3e000000037 0x73f3c38f80000000

def z535 : W := mkw 0xd3b30001ea500000 0x434ecc0007a94000 0xe3f30001f07c0017 0xcb8fcc0007c1f000

def z536 : W := mkw 0x0c4c519805ad8b4c 0x043131466016b62d 0x1c0cd3980f838fe8 0x3470334e603e0e3f

def z537 : W := mkw 0x40b00000a0500000 0x0102c00002814000 0xe0300001f0000004 0x4380c00007c00000

def z538 : W := mkw 0x0015002a846012ea 0x00005400aa11804b 0x033f3c7e006001fd 0x100cfcf1f8018007

def z539 : W := mkw 0x0c485190018d8904 0x0431214640063624 0x1cc0d3800f9f8e2b 0xac73034e003e7e38

def z540 : W := mkw 0xb705fc0b5ea36e4a 0x22dc17f02d7a8db9 0xff0ffc1fff83fe2f 0xeffc3ff07ffe0ff8

def z541 : W := mkw 0xb300ac015a836c00 0x22cc02b0056a0db0 0xe3002c01ff83fe04 0xcf8c00b007fe0ff8

def z542 : W := mkw 0x41b5042bac7036ea 0x0106d410aeb1c0db 0xe3ff3c7ffc7c7fff 0xdf8ffcf1fff1f1ff

def z543 : W := mkw 0xf6b0fae0b056d1b0 0x0bdac3eb82c15b46 0xfff0ffe1f07ff1ff 0xffffc3ff87c1ffc7

def z544 : W := mkw 0xb600f80052834800 0x22d803e0014a0d20 0xfc00d0007f838e2b 0xeff0034001fe0e38

def z545 : W := mkw 0x0400500000000000 0x0010014000000000 0x1c00d0000000002b 0x2070034000000000

def z546 : W := mkw 0x6ce8f35000000000 0x01b3a3cd40000000 0xfcfcf3f80000003f 0x73f3f3cfe0000000

def z547 : W := mkw 0xf3b3a261fa5250b0 0x4bcece8987e94942 0xe3332061f0007004 0x438ccc8187c001c0

def z548 : W := mkw 0xfefffb7e846012ea 0x13fbffedfa11804b 0xfffffffe006001ff 0x73fffffff8018007

def z549 : W := mkw 0xdeea511000000000 0x037ba94440000000 0xffffd3980000003f 0x73ffff4e60000000

def z550 : W := mkw 0x01110423884034a2 0x000444108e2100d2 0x033f3c7f8000703d 0x100cfcf1fe0001c0

def z551 : W := mkw 0x0115042b8c6036ea 0x00045410ae3180db 0x033f3c7f8c007e0c 0x000cfcf1fe3001f8

def z552 : W := mkw 0x2400fbdc00858b4c 0x149003ef7002162d 0x0000fffe00038fe0 0x140003fff8000e3f

def z553 : W := mkw 0xdeea591400000000 0x137ba96450000000 0xffff1c1e0000001f 0x63fffc7078000000

def z554 : W := mkw 0xfeeaff5410836c00 0x33fbabfd50420db0 0xfffffffe0003fe3f 0x77fffffff8000ff8

def z555 : W := mkw 0xf7b0fe61fad37cb0 0x2bdec3f987eb4df2 0xff30fc61ff83fe2f 0xeffcc3f187fe0ff8

def z556 : W := mkw 0xfeeafb5400000000 0x13fbabed50000000 0xffcfdf9e0000000a 0x63ff3f7e78000000

def z557 : W := mkw 0x0100040108002400 0x0004001004200090 0x03001c000c000e08 0x000c007000300038

def z558 : W := mkw 0x0004008805ad8b4c 0x040010022016b62d 0x000c10180fff8ff9 0x9c003040603ffe3f

def z559 : W := mkw 0xd3b30001ea500000 0x434ecc0007a94000 0xff330001ff80000f 0xebfccc0007fe0000

def z560 : W := mkw 0x0c4c511805a90a4c 0x043131446016a429 0x1ccc10180ffc0e1b 0xa8733040603ff038

def z561 : W := mkw 0x0c5c51b8b5ffdbfc 0x0c317146e2d7ff6f 0x1cccd399fffffffb 0xbc73334e67ffffff

def z562 : W := mkw 0xfbffa2c1ff7ec110 0x4beffe8b07fdfb04 0xffffc381ffff801f 0xebffff0e07fffe00

def z563 : W := mkw 0x97005c014a812c00 0x225c0170052a04b0 0xff001c01ff800e0f 0xebfc007007fe0038

def z564 : W := mkw 0xfafaa2e0f35ed1b0 0x4bebea8b83cd7b46 0xfcf0e3e1f3fff1f7 0xfff3c38f87cfffc7

def z565 : W := mkw 0x60b0a2e0b056d1b0 0x0982c28b82c15b46 0xe0f023e1f07c71d4 0x5383c08f87c1f1c7

def z566 : W := mkw 0x6cf8f3f0b056d1b0 0x09b3e3cfc2c15b46 0xfcfcf3f9f07ff1ff 0xfff3f3cfe7c1ffc7

def z567 : W := mkw 0xfeeafbd43016c110 0x1bfbabef50c05b04 0xfcc0c380701f8002 0x6bf3030e01c07e00

def z568 : W := mkw 0xb700fc014a812c00 0x22dc03f0052a04b0 0xff00fc000f800e2f 0x63fc03f0003e0038

def z569 : W := mkw 0xb600fc0052836c00 0x22d803f0014a0db0 0xfc00fc007383fe22 0x6ff003f001ce0ff8

def z570 : W := mkw 0xf7b0fc01fad36c00 0x23dec3f007eb4db0 0xfff0fc01fffffe3f 0xefffc3f007fffff8

def z571 : W := mkw 0x0000000052834800 0x20000000014a0d20 0x0000000073838000 0x0800000001ce0e00

def z572 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000c00000038023 0x8c00030000000e00

def z573 : W := mkw 0xdeea5b5400000000 0x137ba96d50000000 0x1fff1ffe00000018 0x307ffc7ff8000000

def z574 : W := mkw 0x0000000000000000 0x0000000000000000 0x000c101800000039 0x1000304060000000

def z575 : W := mkw 0xf2a2aa4400000000 0x13ca8aa910000000 0xe3f3efe600000037 0x538fcfbf98000000

def z576 : W := mkw 0xf7a2fe455a836c00 0x33de8bf9156a0db0 0xff33fc67ff83fe2f 0xeffccff19ffe0ff8

def z577 : W := mkw 0x0004000804200248 0x0000100020108009 0x000c10180c000e08 0x0000304060300038

def z578 : W := mkw 0x61b0a6e1fad7fdb0 0x2986c29b87eb5ff6 0xe0f0e3e1fffffff7 0xdf83c38f87ffffff

def z579 : W := mkw 0x60a0a2e01006d1b0 0x0982828b80401b46 0xe0f0e3e00003f1f7 0x5783c38f80000fc7

def z580 : W := mkw 0x084c000005280000 0x002130000014a000 0x1c0c00000f800008 0x20703000003e0000

def z581 : W := mkw 0xfbffa261ff7a50b0 0x4beffe8987fde942 0xffff2061fffc701f 0xebfffc8187fff1c0

def z582 : W := mkw 0x084c0080052c8100 0x002130020014b204 0x1cccc3800fff81fb 0xbc73330e003ffe07

def z583 : W := mkw 0x0004000804200248 0x0000100020108009 0x000000000c600fc0 0x840000000031803f

def z584 : W := mkw 0xb715fc01dee36c00 0x22dc57f0077b8db0 0xff3ffc01ffe3fe3f 0xeffcfff007ff8ff8

def z585 : W := mkw 0x011504ab8c64b7ea 0x00045412ae3192df 0x03ffffff8c7fffff 0x9c0ffffffe31ffff

def z586 : W := mkw 0xb700fc815a87ed00 0x22dc03f2056a1fb4 0xffc0ff81ffffffff 0xffff03fe07ffffff

def z587 : W := mkw 0x0d5d51998ded8b4c 0x043575466637b62d 0x1fffd3998fff8fff 0xbc7fff4e663ffe3f

def z588 : W := mkw 0x60a0a24000000000 0x0182828900000000 0xe0c0c38000000002 0x4383030e00000000

def z589 : W := mkw 0x930300014a000000 0x424c0c0005280000 0x0303000000000000 0x000c0c0000000000

def z590 : W := mkw 0x60a0a24030124010 0x0982828900c04900 0xe000000070000000 0x4380000001c00000

def z591 : W := mkw 0xffffffffbc76f7fa 0x1bfffffffef1dbdf 0xfffffffffc7fffff 0xfffffffffff1ffff

def z592 : W := mkw 0x2115a6eb9c66f7fa 0x0884569bae719bdf 0x033fffff8c63fffd 0x940cfffffe318fff

def z593 : W := mkw 0x00100020804010a0 0x0000400082010042 0x033f3c7f806071fd 0x940cfcf1fe0181c7

def z594 : W := mkw 0x97005c015a836c00 0x225c0170056a0db0 0x1f001c01ff83fe08 0xac7c007007fe0ff8

def z595 : W := mkw 0x01110423884034a2 0x000444108e2100d2 0x03333c678c007e2d 0x840cccf19e3001f8

def z596 : W := mkw 0xb700fc015a836c00 0x22dc03f0056a0db0 0x1f00fc000f83fe28 0x247c03f0003e0ff8

def z597 : W := mkw 0xb600f80010024000 0x02d803e000400900 0xff00fc01f003f02f 0xeffc03f007c00fc0

def z598 : W := mkw 0x0400500000810800 0x0010014000020420 0x0000d00000038e20 0x0400034000000e38

def z599 : W := mkw 0x48ff0000a5780000 0x4123fc000295e000 0x1cff00000ffc001b 0xa873fc00003ff000

def z600 : W := mkw 0x01100421884034a0 0x00044010862100d2 0x03303c618c607ffd 0x940cc0f1863181ff

def z601 : W := mkw 0xdaee000005280000 0x036bb8000014a000 0xffff00000ffc001f 0xebfffc00003ff000

def z602 : W := mkw 0xfeeaff7e000036ea 0x13fbabfdf80000db 0xfffffffe00007fff 0x77fffffff80001ff

def z603 : W := mkw 0x0515542b8ce13eea 0x00145550ae3384fb 0x1f3ffc7f8fe3ffff 0xbc7cfff1fe3f8fff

def z604 : W := mkw 0xb704fc895fafef4c 0x26dc13f2257ebfbd 0xff00fc01ffffffef 0xeffc03f007ffffff

def z605 : W := mkw 0x40b002e0a05491b0 0x0902c00b82815246 0x00f0c3e0007f81f3 0x9c03c30f8001fe07

def z606 : W := mkw 0x9f4f5d1f0c20264a 0x127d3d747c308099 0x1f0f1c1e0c000e08 0x207c3c7078300038

def z607 : W := mkw 0x40b00080a0548100 0x0102c00202815204 0xe0f0c381f07f81f7 0xdf83c30e07c1fe07

def z608 : W := mkw 0x49ff0001ef780000 0x4127fc0007bde000 0x00ff0001fffc0010 0x8803fc0007fff000

def z609 : W := mkw 0xd3b70001ee700000 0x434edc0007b9c000 0xe33f0001fc60001d 0xc38cfc0007f18000

def z610 : W := mkw 0xb700fc015a836c00 0x22dc03f0056a0db0 0xe300fc01f003fe24 0x478c03f007c00ff8

def z611 : W := mkw 0x0000035400000000 0x1000000d50000000 0x000003fe00000000 0x1000000ff8000000

def z612 : W := mkw 0x0000000000000000 0x0000000000000000 0x0030206000000035 0x1000c08180000000

def z613 : W := mkw 0x48fa03f4a05491b0 0x1923e80fd2815246 0x00ff03fe007c01d0 0x1003fc0ff801f007

def z614 : W := mkw 0xfeeafb5400000000 0x13fbabed50000000 0xff3f3c7e0000000c 0x63fcfcf1f8000000

def z615 : W := mkw 0x00140028846012e8 0x00005000a211804b 0x003c30798c607ffd 0x9400f0c1e63181ff

def z616 : W := mkw 0x011004a1fad7fdb0 0x2804401287eb5ff6 0x00000001ffffffc0 0x8c00000007ffffff

def z617 : W := mkw 0x40b00000a0500000 0x0102c00002814000 0x00f00000007c0010 0x0003c0000001f000

def z618 : W := mkw 0x0d5d55bb8dedbfee 0x04357556ee37b6ff 0x1cccd3998ffffffb 0xbc73334e663fffff

def z619 : W := mkw 0xfffffee1fffffdb0 0x6bfffffb87fffff6 0xffffffe1ffffffff 0xffffffff87ffffff

def z620 : W := mkw 0xb700f8015a834800 0x22dc03e0056a0d20 0xff00c001ff83800f 0xebfc030007fe0e00

def z621 : W := mkw 0x084c000005280000 0x002130000014a000 0x00cc0000007c0010 0x000330000001f000

def z622 : W := mkw 0x9202080400000000 0x1248082010000000 0x03030c0600000000 0x000c0c3018000000

def z623 : W := mkw 0x2000a00010024000 0x0080028000400900 0x0000e0000003f020 0x0400038000000fc0

def z624 : W := mkw 0x0000000010024000 0x0000000000400900 0x00000001f003f000 0x8c00000007c00fc0

def z625 : W := mkw 0xf7b3fc01fad36c00 0x63decff007eb4db0 0xff33fc01ff83fe2f 0xeffccff007fe0ff8

def z626 : W := mkw 0x0400519800858b4c 0x041001466002162d 0x00c0d398007f8ff3 0x9c03034e6001fe3f

def z627 : W := mkw 0x0100000108000000 0x0004000004200000 0x030000018c00000d 0x800c000006300000

def z628 : W := mkw 0xb600fb5400000000 0x12d803ed50000000 0xff00fffe0000002f 0x73fc03fff8000000

def z629 : W := mkw 0x0c485198018d8b4c 0x043121466006362d 0x1cc0d398039f8fe2 0x3c73034e600e7e3f

def z630 : W := mkw 0x9f4c51994fad8b4c 0x067d3146653eb62d 0xffccd399ffff8fff 0xffff334e67fffe3f

def z631 : W := mkw 0x095d05bb8d6cb7ee 0x04257416ee35b2df 0x03ff3fff8c7c7ffd 0x940ffcfffe31f1ff

def z632 : W := mkw 0x4cfc5198a5fd8b4c 0x0533f1466297f62d 0xfcfcd399ffff8fff 0xfff3f34e67fffe3f

def z633 : W := mkw 0x2400fbf41006d1b0 0x189003efd0401b46 0x0000fffe0003f1e0 0x140003fff8000fc7

def z634 : W := mkw 0x0111000188400000 0x0004440006210000 0x0333000180000004 0x000ccc0006000000

def z635 : W := mkw 0x2400fc2a10837eea 0x209003f0a8420dfb 0x0000fc7e0003ffe0 0x140003f1f8000fff

def z636 : W := mkw 0x2400fc0010836c00 0x209003f000420db0 0xe000fc01f003fe27 0xcf8003f007c00ff8

def z637 : W := mkw 0x010500014f280000 0x40041400053ca000 0x000000000f800000 0x00000000003e0000

def z638 : W := mkw 0xdbfb0001ea500000 0x436fec0007a94000 0xffff0001f000001f 0x63fffc0007c00000

def z639 : W := mkw 0xb700f8014a000000 0x02dc03e005280000 0xff00fc01ff80002f 0xebfc03f007fe0000

def z640 : W := mkw 0x61b1a6e3b856f5b2 0x0986c69b8ee15bd6 0xe3f3efe7f07ff1f7 0xdf8fcfbf9fc1ffc7

def z641 : W := mkw 0x61b5a2e1ff7ed1b0 0x4986d68b87fdfb46 0xe0f0e3e1fffff1f7 0xdf83c38f87ffffc7

def z642 : W := mkw 0x60b4a2e8b5ffdbfc 0x0d82d28ba2d7ff6f 0xe0f0e3e1fffffff7 0xdf83c38f87ffffff

def z643 : W := mkw 0x095d0001ef780000 0x4025740007bde000 0x1ccc0001fffc001b 0xa873300007fff000

def z644 : W := mkw 0xfeeafb5400000000 0x13fbabed50000000 0xfcc0fffe00000022 0x73f303fff8000000

def z645 : W := mkw 0xb700fc015a836c00 0x22dc03f0056a0db0 0xff00ec01f383f006 0x6bfc03b007ce0fc0

def z646 : W := mkw 0x9b4f00014f280000 0x426d3c00053ca000 0xff0f0001ff80000f 0xebfc3c0007fe0000

def z647 : W := mkw 0x60b0a260804010a0 0x0182c28982010042 0xe0f0e3e1806071f7 0xd783c38f860181c7

def z648 : W := mkw 0x0000000000000000 0x0000000000000000 0xe0000001f0000007 0xcb80000007c00000

def z649 : W := mkw 0xdbff0401fffb6c00 0x636ffc1007ffedb0 0xffff0001fffffe1f 0xeffffc0007fffff8

def z650 : W := mkw 0x60b0a260b05250b0 0x0982c28982c14942 0xe0302061f06071f5 0xd780c08187c181c7

def z651 : W := mkw 0xf3b3a2e1fa56d1b0 0x4bcece8b87e95b46 0xe3f3e3e1f07ff1f7 0xdf8fcf8f87c1ffc7

def z652 : W := mkw 0x001000a0b056d1b0 0x0800400282c15b46 0x00c0c381f07ff1f3 0x9c03030e07c1ffc7

def z653 : W := mkw 0xb200a80000000000 0x02c802a000000000 0xe3002c0000000004 0x438c00b000000000

def z654 : W := mkw 0x0115042bdee37eea 0x20045410af7b8dfb 0x033f3c7fffe3fffd 0x9c0cfcf1ffff8fff

def z655 : W := mkw 0x084a011400000000 0x1021280450000000 0x000f001e00000000 0x00003c0078000000

def z656 : W := mkw 0x60b0a260b05250b0 0x0982c28982c14942 0xe030e061f003f027 0xcf80c38187c00fc0

def z657 : W := mkw 0xf7a0fe415a836c00 0x23de83f9056a0db0 0xfff0ffe1ff83fe3f 0xffffc3ff87fe0ff8

def z658 : W := mkw 0xf2b2aa64b05250b0 0x1bcacaa992c14942 0xe3332c67f0007004 0x438cccb19fc001c0

def z659 : W := mkw 0x010500010c200000 0x0004140004308000 0x030f00000c000008 0x000c3c0000300000

def z660 : W := mkw 0x97155c2bcee13eea 0x225c5570af3b84fb 0x1f3f3c7f8fe07ffd 0xb47cfcf1fe3f81ff

def z661 : W := mkw 0x2000a24000000000 0x0080028900000000 0x0000e3e000000020 0x1000038f80000000

def z662 : W := mkw 0x084c019805ad8b4c 0x042130066016b62d 0x00cc03980fff8fd0 0x9c03300e603ffe3f

def z663 : W := mkw 0xfeeafbd43016c110 0x1bfbabef50c05b04 0xfffffffe701f803f 0x7bfffffff9c07e00

def z664 : W := mkw 0x0105040b0c20264a 0x000414102c308099 0x033f3c7e0c000e3d 0x100cfcf1f8300038

def z665 : W := mkw 0x0000002a000012ea 0x00000000a800004b 0x0000007e000001c0 0x10000001f8000007

def z666 : W := mkw 0x60b0a2c0b056c110 0x0982c28b02c15b04 0xe0f0c381f07f8017 0xcb83c30e07c1fe00

def z667 : W := mkw 0x970050014a810800 0x025c0140052a0420 0xff00d001ff838e2f 0xeffc034007fe0e38

def z668 : W := mkw 0xf3b0a2e1fa56d1b0 0x0bcec28b87e95b46 0xfff0e3e1fffff1ff 0xffffc38f87ffffc7

def z669 : W := mkw 0xfffff3f9ffffdbfc 0x4fffffcfe7ffff6f 0xfffff3f9ffffffff 0xffffffcfe7ffffff

def z670 : W := mkw 0xdbff0089effd8b4c 0x476ffc0227bff62d 0xffff0001ffff8fdf 0xeffffc0007fffe3f

def z671 : W := mkw 0xfeeaf800739b4800 0x63fbabe001ce6d20 0xfcc0c000739f8002 0x6bf3030001ce7e00

def z672 : W := mkw 0xbe48f91000000000 0x02f923e440000000 0xffccff980000003f 0x73ff33fe60000000

def z673 : W := mkw 0xb700fd995a87ef4c 0x26dc03f6656a1fbd 0xff00ff99ff83ffef 0xfffc03fe67fe0fff

def z674 : W := mkw 0x0115042b8c6036ea 0x00045410ae3180db 0x003f007f8c607fd0 0x9400fc01fe3181ff

def z675 : W := mkw 0x0115042b8c6036ea 0x00045410ae3180db 0x03003c018c607fed 0x840c00f0063181ff

def z676 : W := mkw 0x011500018c600000 0x0004540006318000 0x033f3c7f8c60003d 0x900cfcf1fe318000

def z677 : W := mkw 0xdbff0081ef7c8100 0x436ffc0207bdf204 0xffffc381ffff81ff 0xffffff0e07fffe07

def z678 : W := mkw 0x00150000a5780000 0x400054000295e000 0x00000000007c0000 0x000000000001f000

def z679 : W := mkw 0x0000000000000000 0x0000000000000000 0x030f1c1e00000008 0x000c3c7078000000

def z680 : W := mkw 0xf7a0fec17a97ed10 0x2bde83fb05ea5fb4 0xffc0ff81ff9ffe2f 0xefff03fe07fe7ff8

def z681 : W := mkw 0xb600f80000000000 0x02d803e000000000 0xff3ffc7e0000003f 0x73fcfff1f8000000

def z682 : W := mkw 0x01150089effd8b4c 0x4404540227bff62d 0x00000001ffff8fc0 0x8c00000007fffe3f

def z683 : W := mkw 0x97005c014a812c00 0x225c0170052a04b0 0x1f003c018f807e2d 0xa47c00f0063e01f8

def z684 : W := mkw 0xdfff5119eff90a4c 0x477ffd4467bfe429 0xffff1019fffc0e1f 0xebfffc4067fff038

def z685 : W := mkw 0x97005c014a812c00 0x225c0170052a04b0 0x1f00dc000f838e2b 0xac7c0370003e0e38

def z686 : W := mkw 0xbe4cf99805ad8b4c 0x06f933e66016b62d 0xffccff980fff8fff 0xffff33fe603ffe3f

def z687 : W := mkw 0xfaeaa24000000000 0x03ebaa8900000000 0xffffe3e00000003f 0x73ffff8f80000000

def z688 : W := mkw 0x0004000005280000 0x000010000014a000 0x000000000ffc0000 0x88000000003ff000

def z689 : W := mkw 0xfaeaaa4400000000 0x13ebaaa910000000 0xffff2c660000001f 0x63fffcb198000000

def z690 : W := mkw 0x9e4e599c05ad8b4c 0x167939667016b62d 0x1fcfdf9e0fff8ffb 0xbc7f3f7e783ffe3f

def z691 : W := mkw 0x095d00018d680000 0x002574000635a000 0x1fff00018ffc001f 0xa87ffc00063ff000

def z692 : W := mkw 0xdfff5111ef780000 0x437ffd4447bde000 0xffffd399fffc003f 0xfbffff4e67fff000

def z693 : W := mkw 0xfffffbf5ff7ed1b0 0x5bffffefd7fdfb46 0xfffffffffffff1ff 0xffffffffffffffc7

def z694 : W := mkw 0x6ceafb5400000000 0x11b3abed50000000 0x00fffffe00000030 0x1003fffff8000000

def z695 : W := mkw 0x49ff0001ad780000 0x4127fc0006b5e000 0x03ff00018c7c001d 0x800ffc000631f000

def z696 : W := mkw 0x011504abbc76f7fa 0x08045412aef1dbdf 0x033f3c7ffc7ffffd 0x9c0cfcf1fff1ffff

def z697 : W := mkw 0xdfff5915ef780000 0x537ffd6457bde000 0xffff1c1ffffc001f 0xebfffc707ffff000

def z698 : W := mkw 0x0848011000000000 0x0021200440000000 0x00cc039800000010 0x1003300e60000000

def z699 : W := mkw 0x0100042b080036ea 0x00040010ac2000db 0x03003c7f8c007fed 0x940c00f1fe3001ff

def z700 : W := mkw 0x60a0a2e03016d1b0 0x0982828b80c05b46 0xe0c0e3e0701ff1e2 0x5f83038f81c07fc7

def z701 : W := mkw 0x01110001ea500000 0x4004440007a94000 0x00000001f0000000 0x0000000007c00000

def z702 : W := mkw 0x2100a40118026400 0x0084029004600990 0xe300fc01fc03fe2f 0xcf8c03f007f00ff8

def z703 : W := mkw 0x40b002e0a05491b0 0x0902c00b82815246 0x00f023e1807c71f5 0x9403c08f8601f1c7

def z704 : W := mkw 0xf3b7ae6f8c6036ea 0x13cedeb9be3180db 0xe33f3c7f8c607ffd 0xd78cfcf1fe3181ff

def z705 : W := mkw 0x0115002b8c6012ea 0x00045400ae31804b 0x033f007f8c6001dd 0x900cfc01fe318007

def z706 : W := mkw 0x40b002e0b056d1b0 0x0902c00b82c15b46 0x00f003e1f07ff1d0 0x9c03c00f87c1ffc7

def z707 : W := mkw 0x0d5955b389cdbda6 0x04356556ce2736f6 0x1ff3efe7839ff006 0x287fcfbf9e0e7fc0

def z708 : W := mkw 0x6ceafb5400000000 0x11b3abed50000000 0x03fffffe0000003d 0x100ffffff8000000

def z709 : W := mkw 0xf2a6aacc05ad8b4c 0x17ca9aab3016b62d 0xe3332c660fff8fc4 0xcf8cccb1983ffe3f

def z710 : W := mkw 0xdbef00016f380000 0x436fbc0005bce000 0xffcf00007ffc001b 0xebff3c0001fff000

def z711 : W := mkw 0xd3a000016a100000 0x034e800005a84000 0xffc00001ff9c000f 0xebff000007fe7000

def z712 : W := mkw 0xfeeafb5410024000 0x13fbabed50400900 0xfffffffe0003f03f 0x77fffffff8000fc0

def z713 : W := mkw 0xdbff042bef7836ea 0x436ffc10afbde0db 0xffff007ffffc7fdf 0xfffffc01fffff1ff

def z714 : W := mkw 0xdbff042bef7836ea 0x436ffc10afbde0db 0xffff3c01fffc7fff 0xeffffcf007fff1ff

def z715 : W := mkw 0xfaeaa24000000000 0x03ebaa8900000000 0xfffffffe0000003f 0x73fffffff8000000

def z716 : W := mkw 0xdbff0423ef7834a2 0x436ffc108fbde0d2 0xffff3c67fffc7e3f 0xeffffcf19ffff1f8

def z717 : W := mkw 0xb700ff555a836c00 0x32dc03fd556a0db0 0xff00ff81ff83fe2f 0xeffc03fe07fe0ff8

def z718 : W := mkw 0xbb4cad995f2ee74c 0x26ed32b6657cbb9d 0xe3cc2f99f07c71d4 0x538f30be67c1f1c7

def z719 : W := mkw 0x60b0aae4b056d1b0 0x1982c2ab92c15b46 0xe0f0efe7f07ff1f7 0xdf83c3bf9fc1ffc7

def z720 : W := mkw 0x2400f3d81087cb5c 0x0c9003cf60421f2d 0x0000d39800038fe0 0x1400034e60000e3f

def z721 : W := mkw 0xfaeaab5400000000 0x13ebaaad50000000 0xe3ffeffe00000037 0x538fffbff8000000

def z722 : W := mkw 0xdafa0000e3580000 0x436be800038d6000 0xffff0001f3fc001f 0xebfffc0007cff000

def z723 : W := mkw 0x0c4c519805ad8b4c 0x043131466016b62d 0x1cc0d3800fff8feb 0xac73034e003ffe3f

def z724 : W := mkw 0xf6a2fb5400000000 0x13da8bed50000000 0xe33ffffe0000003d 0x538cfffff8000000

def z725 : W := mkw 0x2400fca01087fdb0 0x289003f280421ff6 0x0000fc000003ffe0 0x040003f000000fff

def z726 : W := mkw 0xb700fc015a836c00 0x22dc03f0056a0db0 0xfc00fc01ff83fe22 0xeff003f007fe0ff8

def z727 : W := mkw 0xdbff077fef7836ea 0x536ffc1dffbde0db 0xffff3ffffffc7fff 0xfffffcfffffff1ff

def z728 : W := mkw 0xbb4fa2e15f2ed1b0 0x4aed3e8b857cbb46 0x1f0fe3e00f83f1e8 0x347c3f8f803e0fc7

def z729 : W := mkw 0x2400f7fa1087fffe 0x0c9003dfe8421fff 0x0000fffe0003ffe0 0x140003fff8000fff

def z730 : W := mkw 0xfeeafb5452834800 0x33fbabed514a0d20 0xfffffffff383f03f 0xffffffffffce0fc0

def z731 : W := mkw 0x6cfffc00b5fb6c00 0x61b3fff002d7edb0 0x00fffc00007ffe30 0x0403fff00001fff8

def z732 : W := mkw 0xdbff0001ef780000 0x436ffc0007bde000 0xffff1001fffc0e3f 0xeffffc4007fff038

def z733 : W := mkw 0x2400fd901087ed04 0x249003f640421fb4 0x0000ff800003fe20 0x040003fe00000ff8

def z734 : W := mkw 0x0404508804a58b48 0x001011422012962d 0x1cccd3980fff8ffb 0xbc73334e603ffe3f

def z735 : W := mkw 0x61a5a6cb3c36e75a 0x0986969b2cf0db9d 0xe3cfdf9e7c1f8e0a 0x4b8f3f7e79f07e38

def z736 : W := mkw 0xd3b30001ea500000 0x434ecc0007a94000 0xfff30001fffc001f 0xebffcc0007fff000

def z737 : W := mkw 0xdbff042bef7836ea 0x436ffc10afbde0db 0xffff2c67fffc7fdf 0xeffffcb19ffff1ff

def z738 : W := mkw 0x0404508805ad8b4c 0x041011422016b62d 0x1cc0d3800fff8ffb 0xbc73034e003ffe3f

def z739 : W := mkw 0xd2a0000062100000 0x034a800001884000 0xfcc00000739c0002 0x6bf3000001ce7000

def z740 : W := mkw 0xdbfb0001eb580000 0x436fec0007ad6000 0xfff30001f3fc0017 0xebffcc0007cff000

def z741 : W := mkw 0xfeeafb5442000000 0x13fbabed51080000 0xfffffffe7380003f 0x7bfffffff9ce0000

def z742 : W := mkw 0x0c4c519805ad8b4c 0x043131466016b62d 0x1cccfffe0fff8ffb 0xbc7333fff83ffe3f

def z743 : W := mkw 0x2504fd991ca7ef4c 0x249413f664729fbd 0x030cff998c63fffd 0x940c33fe66318fff

def z744 : W := mkw 0xdaea000063180000 0x436ba800018c6000 0xfccc0000739c001b 0x6bf3300001ce7000

def z745 : W := mkw 0xb700fc015a836c00 0x22dc03f0056a0db0 0xff00fc01ffe3ffff 0xfffc03f007ff8fff

def z746 : W := mkw 0xdbff0009ef780248 0x436ffc0027bde009 0xffff0001fffc0fdf 0xeffffc0007fff03f

def z747 : W := mkw 0x48fd03faa57c93fe 0x0d23f40fea95f24f 0x00ff03fe007c01d0 0x1003fc0ff801f007

def z748 : W := mkw 0xfeeafb5420100000 0x13fbabed50804000 0xfffffffe701c003f 0x7bfffffff9c07000

def z749 : W := mkw 0x64a0fb5400000000 0x119283ed50000000 0xe3fffffe0000003f 0x538ffffff8000000

def z750 : W := mkw 0x9b5d042bcf6836ea 0x026d7410af3da0db 0xffff3c7ffffc7fff 0xfffffcf1fffff1ff

def z751 : W := mkw 0xdbff0241ef780000 0x436ffc0907bde000 0xffff03e1fffc001f 0xfbfffc0f87fff000

def z752 : W := mkw 0xdaea042a631836ea 0x436ba810a98c60db 0xfcc03c7e739c7fe2 0x7ff300f1f9ce71ff

def z753 : W := mkw 0xb700fc015a836c00 0x22dc03f0056a0db0 0xff00fc7fff83fe2f 0xfffc03f1fffe0ff8

def z754 : W := mkw 0x2400f3f01087d9b4 0x0c9003cfc0421f66 0x0000e3e00003f1e0 0x1400038f80000fc7

def z755 : W := mkw 0x011504abfef7fffa 0x28045412affbdfff 0x00000001ffffffc0 0x8c00000007ffffff

def z756 : W := mkw 0x9b5d0001ef780000 0x426d740007bde000 0xffcc0001fffc001f 0xebff300007fff000

def z757 : W := mkw 0xdbff0111ef780000 0x436ffc0447bde000 0xffff0399fffc001f 0xfbfffc0e67fff000

def z758 : W := mkw 0xdaea000063180000 0x436ba800018c6000 0xfcf00000739c0017 0x6bf3c00001ce7000

def z759 : W := mkw 0xb300a4015a836c00 0x22cc0290056a0db0 0xff00e001ff83fe2f 0xeffc038007fe0ff8

def z760 : W := mkw 0x60b0a2e0b056d1b0 0x0982c28b82c15b46 0xe0f0e3e1f07ff1d6 0x5b83c38f87c1ffc7

def z761 : W := mkw 0x9e5a59b4b056d1b0 0x1a796966d2c15b46 0x1f0f1c1ff07ff1c8 0xac7c3c707fc1ffc7

def z762 : W := mkw 0xb703fc015a836c00 0x62dc0ff0056a0db0 0xff03fc01ff83fe2f 0xeffc0ff007fe0ff8

def z763 : W := mkw 0xb700fd115a836c00 0x22dc03f4456a0db0 0xff00ff99ff83fe2f 0xfffc03fe67fe0ff8

def z764 : W := mkw 0xd7b35199ead58b4c 0x475ecd4667ab562d 0xe333d399f0038fe4 0x578ccf4e67c00e3f

def z765 : W := mkw 0xdbff0021ef7810a0 0x436ffc0087bde042 0xffff3c7ffffc71ff 0xfffffcf1fffff1c7

def z766 : W := mkw 0xbe48f91000000000 0x02f923e440000000 0xfffffffe0000003f 0x73fffffff8000000

def z767 : W := mkw 0x9f4d5d1b4fa92e4e 0x267d35746d3ea4b9 0x1f0f1c1e0f800e08 0x207c3c70783e0038

def z768 : W := mkw 0xdbef00016f380000 0x436fbc0005bce000 0xffff00007f9c001f 0x6bfffc0001fe7000

def z769 : W := mkw 0x6cfcf378b5fb5afc 0x0db3f3cde2d7ed6b 0xfc3c3079ff807e0c 0x63f0f0c1e7fe01f8

def z770 : W := mkw 0x084c008805ad8b4c 0x042130022016b62d 0x1cccc3800fff8ffb 0xbc73330e003ffe3f

def z771 : W := mkw 0x9f4f551b4fa92e4e 0x467d3d546d3ea4b9 0x1f0f1c1e0f800e08 0x207c3c70783e0038

def z772 : W := mkw 0xdaea000063180000 0x436ba800018c6000 0xfcc000007f9c000b 0xebf3000001fe7000

def z773 : W := mkw 0xd3b70001ef780000 0x434edc0007bde000 0xff330001fffc000f 0xebfccc0007fff000

def z774 : W := mkw 0xdbff0001ef780000 0x436ffc0007bde000 0xffffc001ffff803f 0xefffff0007fffe00

def z775 : W := mkw 0xfeeafb5400000000 0x13fbabed50000000 0xffff3ffe0000001c 0x73fffcfff8000000

def z776 : W := mkw 0xdbea00016b180000 0x436fa80005ac6000 0xffc00001f39c0006 0x6bff000007ce7000

def z777 : W := mkw 0x40b000a0b056d1b0 0x0902c00282c15b46 0xe0f0c381f07ff1f7 0xdf83c30e07c1ffc7

def z778 : W := mkw 0xdbff042bef7836ea 0x436ffc10afbde0db 0xfcc00001fffc7fc2 0xeff3000007fff1ff

def z779 : W := mkw 0x9315042bef7836ea 0x424c5410afbde0db 0xff3f3c7ffffc7fff 0xfffcfcf1fffff1ff

def z780 : W := mkw 0x00140028846012e8 0x00005000a211804b 0x033f3c7f8c607ffd 0x940cfcf1fe3181ff

def z781 : W := mkw 0xdbfb0001eb580000 0x436fec0007ad6000 0xffff0001f39c001f 0x6bfffc0007ce7000

def z782 : W := mkw 0xdbff0001ef780000 0x436ffc0007bde000 0xffff2001fffc703f 0xeffffc8007fff1c0

def z783 : W := mkw 0xfeeafb5400000000 0x13fbabed50000000 0xffffdffe0000001a 0x73ffff7ff8000000

def z784 : W := mkw 0xdafa0020e35810a0 0x436be800838d6042 0xfcf02061f3fc71f7 0xfff3c08187cff1c7

def z785 : W := mkw 0x2400f2e01087d9b0 0x089003cb80421f66 0x0000f3e00003ffe0 0x140003cf80000fff

def z786 : W := mkw 0x0400511000000000 0x0010014440000000 0x033ffffe0000003d 0x100cfffff8000000

def z787 : W := mkw 0x970054014a812c00 0x025c0150052a04b0 0xff00fc01ff83fe2f 0xeffc03f007fe0ff8

def z788 : W := mkw 0xf3b1ae63fa5274b2 0x2bcec6b98fe949d2 0xe3332c67f0007004 0x438cccb19fc001c0

def z789 : W := mkw 0x2010a0a09046d1a0 0x0080428282411b46 0xe0f0e3e1f07ff1f7 0xdf83c38f87c1ffc7

def z790 : W := mkw 0xfeeafb5400000000 0x13fbabed50000000 0xff3ffffe0000002c 0x73fcfffff8000000

def z791 : W := mkw 0x2400fc0010836c00 0x209003f000420db0 0xfc00fc01ff83fe2f 0xeff003f007fe0ff8

def z792 : W := mkw 0x97005c015a836c00 0x225c0170056a0db0 0xff001c01ff83fe0f 0xeffc007007fe0ff8

def z793 : W := mkw 0x60a0a2c01006c100 0x0182828b00401b04 0xe0f0e3e1f07ff1f7 0xdf83c38f87c1ffc7

def z794 : W := mkw 0xffffff7f8c6036ea 0x13fffffdfe3180db 0xfcc0c3818c607fc2 0xe7f3030e063181ff

def z795 : W := mkw 0xdbff040bef78264a 0x436ffc102fbde099 0xffff3c1ffffc7e3f 0xeffffcf07ffff1f8

def z796 : W := mkw 0xdbea00016b180000 0x436fa80005ac6000 0xffff0001ff9c001f 0xebfffc0007fe7000

def z797 : W := mkw 0x48ff02eaa57c93fa 0x4923fc0baa95f24f 0x00ff03fe007c01d0 0x1003fc0ff801f007

def z798 : W := mkw 0xdbfa0001ea500000 0x036fe80007a94000 0xffff0001fffc001f 0xebfffc0007fff000

def z799 : W := mkw 0x9b5f0001ef780000 0x426d7c0007bde000 0xff0f0001fffc000f 0xebfc3c0007fff000

def z800 : W := mkw 0xfeeafb5400000000 0x13fbabed50000000 0xfffffffe006001ff 0xf7fffffff8018007

def z801 : W := mkw 0x2000a2e01006d1b0 0x0880028b80401b46 0xe0c0e3e1f07ff1f7 0xdf83038f87c1ffc7

def z802 : W := mkw 0x2515feeb9ce7fffa 0x289457fbae739fff 0x033fffff8c63fffd 0x940cfffffe318fff

def z803 : W := mkw 0xd3b50001ef780000 0x434ed40007bde000 0xfff00001fffc001f 0xebffc00007fff000

def z804 : W := mkw 0x60b0a2e0b056d1b0 0x0982c28b82c15b46 0xe0f0e3e1f07ff1c6 0xcf83c38f87c1ffc7

def z805 : W := mkw 0xb700ff555a836c00 0x32dc03fd556a0db0 0xff3fffffff83fe3f 0xfffcfffffffe0ff8

def z806 : W := mkw 0x49fd0001ef780000 0x4127f40007bde000 0xfcfc0001fffc001f 0xebf3f00007fff000

def z807 : W := mkw 0x0004042a042036ea 0x00001010a81080db 0x033f3c7e0c607ffd 0x940cfcf1f83181ff

def z808 : W := mkw 0xdbfb0001eb580000 0x436fec0007ad6000 0xfff30001ff9c000f 0xebffcc0007fe7000

def z809 : W := mkw 0xdbff0401ef782400 0x436ffc1007bde090 0xffff0001fffc7e1f 0xeffffc0007fff1f8

def z810 : W := mkw 0xfeeafb5421180000 0x53fbabed50846000 0xfffffffe001c003f 0x73fffffff8007000

def z811 : W := mkw 0xfeeafb5410834800 0x33fbabed50420d20 0xfffffffe0003803f 0x73fffffff8000e00

def z812 : W := mkw 0x0115042b8c6036ea 0x00045410ae3180db 0x033ffc7f8c63ffff 0x9c0cfff1fe318fff

def z813 : W := mkw 0x01100421884034a0 0x00044010862100d2 0x033f3c7f8c607ffd 0x940cfcf1fe3181ff

def z814 : W := mkw 0xb615f82ad6e35aea 0x22d857e0ab5b8d6b 0xfc3fc07e73e381d2 0x7bf0ff01f9cf8e07

def z815 : W := mkw 0xdbff0001ef780000 0x436ffc0007bde000 0xfccc0001fffc001b 0xebf3300007fff000

def z816 : W := mkw 0xfeeafb5400000000 0x13fbabed50000000 0xe3fffffe00000034 0x538ffffff8000000

def z817 : W := mkw 0xdaea000063180000 0x436ba800018c6000 0xfcff0000739c0012 0x6bf3fc0001ce7000

def z818 : W := mkw 0xdbff0021ef7810a0 0x436ffc0087bde042 0xffff0001fffc71df 0xeffffc0007fff1c7

def z819 : W := mkw 0x60b0a2e0b056d1b0 0x0982c28b82c15b46 0xe0f0fffff07ff1f7 0xdf83c3ffffc1ffc7

def z820 : W := mkw 0xf3b2ae65fa5274b0 0x3bcecab997e949d2 0xe3332c67f0007004 0x438cccb19fc001c0

def z821 : W := mkw 0x49ea07555a836c00 0x3127a81d556a0db0 0x00ff03ffff83fe10 0x9c03fc0ffffe0ff8

def z822 : W := mkw 0xdaea035463180000 0x536ba80d518c6000 0xfcc00380739c0002 0x6bf3000e01ce7000

def z823 : W := mkw 0xd7b05ee1ead5bdb0 0x2b5ec17b87ab56f6 0x1ff01fe00ffc0fd8 0x307fc07f803ff03f

def z824 : W := mkw 0x2510fee198c7fdb0 0x289443fb86631ff6 0x0330ffe18c63fffd 0x940cc3ff86318fff

def z825 : W := mkw 0x011504ab8ce5bfee 0x04045412ae3396ff 0x000000018c63ffc0 0x8400000006318fff

def z826 : W := mkw 0xb700fd155a836c00 0x32dc03f4556a0db0 0xff00fc1fff83fe2f 0xeffc03f07ffe0ff8

def z827 : W := mkw 0xdbff0001ef780000 0x436ffc0007bde000 0xfcf00001fffc0017 0xebf3c00007fff000

def z828 : W := mkw 0xdaea000063180000 0x436ba800018c6000 0xfcc0000073fc0013 0xebf3000001cff000

def z829 : W := mkw 0xdbff0c01ef782400 0x636ffc3007bde090 0xffff0c01fffc001f 0xebfffc3007fff000

def z830 : W := mkw 0x2400fff41087fdb0 0x389003ffd0421ff6 0x0000fffe0003ffe0 0x140003fff8000fff

def z831 : W := mkw 0xfeeafb5401080000 0x13fbabed50042000 0xfffffffe039c003f 0x7bfffffff80e7000

def z832 : W := mkw 0xdbff040bef78264a 0x436ffc102fbde099 0xffff3c7ffffc0e3f 0xfbfffcf1fffff038

def z833 : W := mkw 0x60b0a2e0b056d1b0 0x0982c28b82c15b46 0xe0c0e381f07ff1e7 0xcf83038e07c1ffc7

def z834 : W := mkw 0x60b0a2e0b056d1b0 0x0982c28b82c15b46 0xfcf0e3e1fffff1ff 0xfff3c38f87ffffc7

def z835 : W := mkw 0xfeeafb5462100000 0x53fbabed51884000 0xfffffffe7000003f 0x73fffffff9c00000

def z836 : W := mkw 0xb700fc015a836c00 0x22dc03f0056a0db0 0xff0cfc19ff83fe3f 0xfffc33f067fe0ff8

def z837 : W := mkw 0xb300a4015a026400 0x02cc029005680990 0xff00fc01ff83fe2f 0xeffc03f007fe0ff8

def z838 : W := mkw 0x9a48000043080000 0x02692000010c2000 0xfcc00000739c0002 0x6bf3000001ce7000

def z839 : W := mkw 0x011504ab8c64b7ea 0x00045412ae3192df 0x000000018c7fffc0 0x8c0000000631ffff

def z840 : W := mkw 0xdbff0001ef780000 0x436ffc0007bde000 0xffffc381fffc003f 0xfbffff0e07fff000

def z841 : W := mkw 0xdbff002bef7812ea 0x436ffc00afbde04b 0xffff3c7ffffc01ff 0xfbfffcf1fffff007

def z842 : W := mkw 0xdbff0805ef780000 0x536ffc2017bde000 0xffff0c07fffc001f 0xebfffc301ffff000

def z843 : W := mkw 0x0115042bcf6836ea 0x40045410af3da0db 0x033f3c7f8fe07ffd 0x940cfcf1fe3f81ff

def z844 : W := mkw 0x2515fb55ef780000 0x509457ed57bde000 0x0000fffffffc0020 0x980003fffffff000

def z845 : W := mkw 0xfeeafb5410024000 0x13fbabed50400900 0xfffffffe7003803f 0x7bfffffff9c00e00

def z846 : W := mkw 0x0115042bee7036ea 0x40045410afb9c0db 0x033f3c7ffc607ffd 0x940cfcf1fff181ff

def z847 : W := mkw 0x0015042a846036ea 0x00005410aa1180db 0x033f3c7e00607ffd 0x140cfcf1f80181ff

def z848 : W := mkw 0xdaea000063180000 0x436ba800018c6000 0xffc00000739c000f 0x6bff000001ce7000

def z849 : W := mkw 0x011504abff7ef7fa 0x48045412affdfbdf 0x00000001ffffffc0 0x8c00000007ffffff

def z850 : W := mkw 0xdbfc0001ef780000 0x036ff00007bde000 0xfffc0001fffc001f 0xebfff00007fff000

def z851 : W := mkw 0xdbff0021ef7810a0 0x436ffc0087bde042 0xffff0061fffc01df 0xfbfffc0187fff007

def z852 : W := mkw 0x93150001ef780000 0x424c540007bde000 0xfc000001fffc0002 0xebf0000007fff000

def z853 : W := mkw 0x2400fbfc1087dbfc 0x1c9003eff0421f6f 0x0000fffe0003ffe0 0x140003fff8000fff

def z854 : W := mkw 0x48fc0028a57812e8 0x0123f000a295e04b 0xfcfc3079fffc7fff 0xfff3f0c1e7fff1ff

def z855 : W := mkw 0x010404090c202648 0x0004101024308099 0x033f3c7f8c607ffd 0x940cfcf1fe3181ff

def z856 : W := mkw 0x0010042a804036ea 0x00004010aa0100db 0x033f3c7f80607ffd 0x940cfcf1fe0181ff

def z857 : W := mkw 0xb700fc015a836c00 0x22dc03f0056a0db0 0xfc00e001ff83fe27 0xeff0038007fe0ff8

def z858 : W := mkw 0xdbea00016b180000 0x436fa80005ac6000 0xffc000007f9c000a 0x6bff000001fe7000

def z859 : W := mkw 0xdeea511000000000 0x037ba94440000000 0xfffffffe0000003f 0x73fffffff8000000

def z860 : W := mkw 0x011504abbdfffffe 0x0c045412aef7ffff 0x00000001ffffffc0 0x8c00000007ffffff

def z861 : W := mkw 0xdaff0000e7780000 0x436bfc00039de000 0xfcff0001f3fc0017 0xebf3fc0007cff000

def z862 : W := mkw 0x930004015a836c00 0x224c0010056a0db0 0xff003c01ff83fe2f 0xeffc00f007fe0ff8

def z863 : W := mkw 0x930000014a000000 0x024c000005280000 0xffc00001fffc001f 0xebff000007fff000

def z864 : W := mkw 0x2400fff81087fffc 0x2c9003ffe0421fff 0x0000fff80003ffe0 0x140003ffe0000fff

def z865 : W := mkw 0xb300ac015a836c00 0x22cc02b0056a0db0 0xff002c01ff83fe0f 0xeffc00b007fe0ff8

def z866 : W := mkw 0x0c4f519805ad8b4c 0x44313d466016b62d 0x1ccfd3980fff8ffb 0xbc733f4e603ffe3f

def z867 : W := mkw 0xb700fc015a836c00 0x22dc03f0056a0db0 0xff00fc01ff83fe0e 0x6bfc03f007fe0ff8

def z868 : W := mkw 0x0c4c519805ad8b4c 0x043131466016b62d 0x1cccc3980fff8fd2 0xbc73330e603ffe3f

def z869 : W := mkw 0x0c4c519805ad8b4c 0x043131466016b62d 0x1cccc3800fff8fdb 0xac73330e003ffe3f

def z870 : W := mkw 0xfeeafb5400000000 0x13fbabed50000000 0xfffffffff000003f 0xfbffffffffc00000

def z871 : W := mkw 0x0000000000000000 0x0000000000000000 0x03fffffe0000003f 0x100ffffff8000000

def z872 : W := mkw 0xb700fc015a836c00 0x22dc03f0056a0db0 0xfc00d001ff83fe2b 0xeff0034007fe0ff8

def z873 : W := mkw 0xdbff0355ef780000 0x536ffc0d57bde000 0xffff3ffffffc003f 0xfbfffcfffffff000

def z874 : W := mkw 0xdbff0001ef780000 0x436ffc0007bde000 0xfcff0001fffc0012 0xebf3fc0007fff000

def z875 : W := mkw 0x60a0a2c03016c110 0x0982828b00c05b04 0xe0c0e381f07ff1f7 0xdf83038e07c1ffc7

def z876 : W := mkw 0xb700fc015a836c00 0x22dc03f0056a0db0 0xff33fc67ff83fe2f 0xeffccff19ffe0ff8

def z877 : W := mkw 0x084c0088052c8348 0x002130022014b20d 0x1cccd3980fff8ffb 0xbc73334e603ffe3f

def z878 : W := mkw 0xdaea035400000000 0x136ba80d50000000 0xffff3ffe0000003f 0x73fffcfff8000000

def z879 : W := mkw 0x011504abeffdbfee 0x44045412afbff6ff 0x00000001ffffffc0 0x8c00000007ffffff

def z880 : W := mkw 0x0c4c519805ad8b4c 0x043131466016b62d 0x1fffd3980fff8fff 0xbc7fff4e603ffe3f

def z881 : W := mkw 0xdbff0423ef7834a2 0x436ffc108fbde0d2 0xffff3c7ffffc703f 0xfbfffcf1fffff1c0

def z882 : W := mkw 0x9b5d0001cf680000 0x026d7400073da000 0xffff0001fffc001f 0xebfffc0007fff000

def z883 : W := mkw 0xd2b00000e2500000 0x034ac00003894000 0xfcf00001f3fc0017 0xebf3c00007cff000

def z884 : W := mkw 0xb700fc015a836c00 0x22dc03f0056a0db0 0xffc0ff81ff83fe3f 0xffff03fe07fe0ff8

def z885 : W := mkw 0x48ff01baa57c93ee 0x4523fc06ea95f24f 0x00ff03fe007c01d0 0x1003fc0ff801f007

def z886 : W := mkw 0xdaee000867380248 0x436bb800219ce009 0xfccc10187ffc0ffb 0xfff3304061fff03f

def z887 : W := mkw 0x2515fdbb9ce7ffee 0x249457f6ee739fff 0x033fffff8c63fffd 0x940cfffffe318fff

def z888 : W := mkw 0x0c4c519805ad8b4c 0x043131466016b62d 0x1cccd3980fff8ff8 0x3473334e603ffe3f

def z889 : W := mkw 0x011504ab9c66f7fa 0x08045412ae719bdf 0x000000018c63ffc0 0x8400000006318fff

def z890 : W := mkw 0xdbff0001ef780000 0x436ffc0007bde000 0xffff1019fffc003f 0xfbfffc4067fff000

def z891 : W := mkw 0x0115042b8d6836ea 0x00045410ae35a0db 0x033f3c7f8ffc7ffd 0x9c0cfcf1fe3ff1ff

def z892 : W := mkw 0xfeeafb54739b4800 0x73fbabed51ce6d20 0xfffffffe739f803f 0x7bfffffff9ce7e00

def z893 : W := mkw 0x60b0a2e0b056d1b0 0x0982c28b82c15b46 0xe0c0e3e1f07ff1e2 0xdf83038f87c1ffc7

def z894 : W := mkw 0xdaea000063180000 0x436ba800018c6000 0xffcf0000739c000a 0x6bff3c0001ce7000

def z895 : W := mkw 0x48ea035400000000 0x1123a80d50000000 0x03ff2ffe00000014 0x100ffcbff8000000

def z896 : W := mkw 0xd3b50001ee700000 0x034ed40007b9c000 0xffff0001fffc001f 0xebfffc0007fff000

def z897 : W := mkw 0xdbff042bef7836ea 0x436ffc10afbde0db 0xffff2c7ffffc71df 0xfbfffcb1fffff1c7

def z898 : W := mkw 0xdbfb0423eb5834a2 0x436fec108fad60d2 0xfff32c67f39c7006 0x6bffccb19fce71c0

def z899 : W := mkw 0x2414f3f894e7dbfc 0x0c9053cfe2539f6f 0x003cf3f98c63fffd 0x9400f3cfe6318fff

def z900 : W := mkw 0x0115042bac7036ea 0x00045410aeb1c0db 0x033f3c7ffc7c7ffd 0x9c0cfcf1fff1f1ff

def z901 : W := mkw 0xb700fe415a836c00 0x22dc03f9056a0db0 0xff00ffe1ff83fe2f 0xfffc03ff87fe0ff8

def z902 : W := mkw 0xfeeafb5443080000 0x53fbabed510c2000 0xfffffffe0380003f 0x73fffffff80e0000

def z903 : W := mkw 0x0c4c519805ad8b4c 0x043131466016b62d 0x1cccd3980fff8fca 0xac73334e603ffe3f

def z904 : W := mkw 0x93150001ef780000 0x424c540007bde000 0xff3f0001fffc001f 0xebfcfc0007fff000

def z905 : W := mkw 0xdaea000063180000 0x436ba800018c6000 0xfff30000739c0006 0x6bffcc0001ce7000

def z906 : W := mkw 0xb700fc015a836c00 0x22dc03f0056a0db0 0xff00fc01ff83fe2c 0x67fc03f007fe0ff8

def z907 : W := mkw 0xdbff0009ef780248 0x436ffc0027bde009 0xffff0019fffc01df 0xfbfffc0067fff007

def z908 : W := mkw 0x60b0a2e0b056d1b0 0x0982c28b82c15b46 0xe0f0c381f07ff1d7 0xcf83c30e07c1ffc7

def z909 : W := mkw 0x40b000a0a05491a0 0x0102c00282815246 0xe0f0e3e1f07ff1f7 0xdf83c38f87c1ffc7

def z910 : W := mkw 0xdbff0001ef780000 0x436ffc0007bde000 0xffff3c01fffc003f 0xebfffcf007fff000

def z911 : W := mkw 0xdbff0001ef780000 0x436ffc0007bde000 0xffff007ffffc001f 0xfbfffc01fffff000

def z912 : W := mkw 0x011504abac74b7fa 0x08045412aeb1d2df 0x000000018c7c7fc0 0x840000000631f1ff

def z913 : W := mkw 0x40a0024000000000 0x0102800900000000 0x03ff3ffe0000003d 0x100ffcfff8000000

def z914 : W := mkw 0xb700fc015a836c00 0x22dc03f0056a0db0 0xff30fc61ff83fe3f 0xfffcc3f187fe0ff8

def z915 : W := mkw 0xfeeafbd4319fc914 0x1ffbabef50c67f24 0xfcc0c380739f8002 0x6bf3030e01ce7e00

def z916 : W := mkw 0xfeeafb5400810800 0x13fbabed50020420 0xfffffffe0f800e3f 0x73fffffff83e0038

def z917 : W := mkw 0xdeea5b5400000000 0x137ba96d50000000 0xffff1ffe0000001f 0x73fffc7ff8000000

def z918 : W := mkw 0xb600f80052834800 0x22d803e0014a0d20 0xfc00f001ff83fe2f 0xeff003c007fe0ff8

def z919 : W := mkw 0xf2a2aa4400000000 0x13ca8aa910000000 0xe3fffffe0000003f 0x538ffffff8000000

def z920 : W := mkw 0x40b00000a0500000 0x0102c00002814000 0xfcf00001fffc001f 0xebf3c00007fff000

def z921 : W := mkw 0x60b2a2e4b056d1b0 0x1982ca8b92c15b46 0xe0f3e3e7f07ff1f7 0xdf83cf8f9fc1ffc7

def z922 : W := mkw 0x2400f9901087c904 0x249003e640421f24 0x0000c38000038000 0x0000030e00000e00

def z923 : W := mkw 0x0c4c519805ad8b4c 0x043131466016b62d 0x1cccd3980fff8fda 0x3873334e603ffe3f

def z924 : W := mkw 0xdaea000063180000 0x436ba800018c6000 0xffff3c7e739c003f 0x7bfffcf1f9ce7000

def z925 : W := mkw 0xdaff0000e7780000 0x436bfc00039de000 0xfcc0000073fc0002 0x6bf3000001cff000

def z926 : W := mkw 0xdbff0403ef782402 0x436ffc100fbde090 0xffff0c07fffc001f 0xebfffc301ffff000

def z927 : W := mkw 0xb700fc015a836c00 0x22dc03f0056a0db0 0xff003c01ff83fe0c 0xeffc00f007fe0ff8

def z928 : W := mkw 0xdbff0001ef780000 0x436ffc0007bde000 0xffff2c67fffc001f 0xebfffcb19ffff000

def z929 : W := mkw 0xfeeafbd47297c910 0x3bfbabef51ca5f24 0xfcc0c380739f8002 0x6bf3030e01ce7e00

def z930 : W := mkw 0x2000a24000000000 0x0080028900000000 0x033ffffe0000003d 0x100cfffff8000000

def z931 : W := mkw 0x60b0a2e0b056d1b0 0x0982c28b82c15b46 0xe3ffe3e1f07ff1ff 0xdf8fff8f87c1ffc7

def z932 : W := mkw 0xf3b3a663fa5274b2 0x4bcece998fe949d2 0xe3332c67f0007004 0x438cccb19fc001c0

def z933 : W := mkw 0x0c4c519805ad8b4c 0x043131466016b62d 0x1cffd3fe0fff8ffb 0xbc73ff4ff83ffe3f

def z934 : W := mkw 0x0115042b8c6036ea 0x00045410ae3180db 0x033f3c7f8c007fec 0x140cfcf1fe3001ff

def z935 : W := mkw 0xdbff042bef7836ea 0x436ffc10afbde0db 0xffff1c1ffffc7fdf 0xeffffc707ffff1ff

def z936 : W := mkw 0xdbff0423ef7834a2 0x436ffc108fbde0d2 0xffff0001fffc701f 0xebfffc0007fff1c0

def z937 : W := mkw 0xfeeafbd4538fc904 0x37fbabef514e3f24 0xfcc0c380739f8002 0x6bf3030e01ce7e00

def z938 : W := mkw 0xdbff0021ef7810a0 0x436ffc0087bde042 0xffff2061fffc701f 0xebfffc8187fff1c0

def z939 : W := mkw 0xdbff0401ef782400 0x436ffc1007bde090 0xffff1c01fffc0e1f 0xebfffc7007fff038

def z940 : W := mkw 0x2400fac01087c910 0x289003eb00421f24 0x0000c38000038000 0x0000030e00000e00

def z941 : W := mkw 0x0c4c519805ad8b4c 0x043131466016b62d 0x1fcfdf9e0fff8ffb 0xbc7f3f7e783ffe3f

def z942 : W := mkw 0xbe4afb5400000000 0x12f92bed50000000 0x1f3ffffe0000003d 0x307cfffff8000000

def z943 : W := mkw 0x930400014f280000 0x024c1000053ca000 0xff000001fffc000f 0xebfc000007fff000

def z944 : W := mkw 0x9315042bef7836ea 0x424c5410afbde0db 0xff003c01fffc7fef 0xeffc00f007fff1ff

def z945 : W := mkw 0x9b4f00014f280000 0x426d3c00053ca000 0xffcf0001fffc001f 0xebff3c0007fff000

def z946 : W := mkw 0xdaee000067380000 0x436bb800019ce000 0xfcc000007ffc0002 0xebf3000001fff000

def z947 : W := mkw 0x60b0a2e0b056d1b0 0x0982c28b82c15b46 0xe0fcf3f9f07ff1ff 0xdf83f3cfe7c1ffc7

def z948 : W := mkw 0xdaff0000e7780000 0x436bfc00039de000 0xfcff00007ffc001b 0xebf3fc0001fff000

def z949 : W := mkw 0x0115042b8c6036ea 0x00045410ae3180db 0x03ff3c7f8c7c7fff 0x9c0ffcf1fe31f1ff

def z950 : W := mkw 0xb700f0015a834800 0x02dc03c0056a0d20 0xff00f001ff83fe2f 0xeffc03c007fe0ff8

def z951 : W := mkw 0xdbff0001ef780000 0x436ffc0007bde000 0xffff0001f3fc0016 0x6bfffc0007cff000

def z952 : W := mkw 0x0115042b8c6036ea 0x00045410ae3180db 0x1f3f3c7f8fe07fff 0xbc7cfcf1fe3f81ff

def z953 : W := mkw 0x0115042b8c6036ea 0x00045410ae3180db 0x03ffffff8c607fff 0x940ffffffe3181ff

def z954 : W := mkw 0xfeeafb5400000000 0x13fbabed50000000 0x1ffffffe00000038 0x307ffffff8000000

def z955 : W := mkw 0x0c485190018d8904 0x0431214640063624 0x1cc0d3800fff8ffb 0xbc73034e003ffe3f

def z956 : W := mkw 0xb700fc015a836c00 0x22dc03f0056a0db0 0xff3ffc01ff83fe3f 0xeffcfff007fe0ff8

def z957 : W := mkw 0xfeeafb5430124010 0x1bfbabed50c04900 0xfffffffe7000003f 0x73fffffff9c00000

def z958 : W := mkw 0xb600fb5400000000 0x12d803ed50000000 0xff3ffffe0000003f 0x73fcfffff8000000

def z959 : W := mkw 0xfeeafb5410024000 0x13fbabed50400900 0xfffffffff000703f 0x73ffffffffc001c0

def z960 : W := mkw 0xb700fe455a836c00 0x32dc03f9156a0db0 0xff00fc67ff83fe2f 0xeffc03f19ffe0ff8

def z961 : W := mkw 0x2400feea1087fffa 0x289003fba8421fff 0x0000fffe0003ffe0 0x140003fff8000fff

def z962 : W := mkw 0x48ff0000a5780000 0x4123fc000295e000 0xfcff0001fffc001f 0xebf3fc0007fff000

def z963 : W := mkw 0x0c4c519805ad8b4c 0x043131466016b62d 0xfcccd399ffff8fff 0xfff3334e67fffe3f

def z964 : W := mkw 0xb700fc015a836c00 0x22dc03f0056a0db0 0xff00ec01ff83fe06 0xeffc03b007fe0ff8

def z965 : W := mkw 0xdbff0001ef780000 0x436ffc0007bde000 0xffcf0001fffc000a 0xebff3c0007fff000

def z966 : W := mkw 0x60b0a2e0b056d1b0 0x0982c28b82c15b46 0xe0ffe3fff07ff1f7 0xdf83ff8fffc1ffc7

def z967 : W := mkw 0x9200000063180000 0x42480000018c6000 0xfc000000739c0002 0x6bf0000001ce7000

def z968 : W := mkw 0x60b3a2e0b056d1b0 0x4982ce8b82c15b46 0xe0f3e3e1f07ff1f7 0xdf83cf8f87c1ffc7

def z969 : W := mkw 0xdbff0261ef7810b0 0x4b6ffc0987bde042 0xffff0061fffc001f 0xebfffc0187fff000

def z970 : W := mkw 0x9e4a591400000000 0x1279296450000000 0x1ffffffe0000003f 0x307ffffff8000000

def z971 : W := mkw 0xf6a0fa4000000000 0x03da83e900000000 0xfffffffe0000003f 0x73fffffff8000000

def z972 : W := mkw 0xdbff042bef7836ea 0x436ffc10afbde0db 0xffff1c7ffffc0fdf 0xfbfffc71fffff03f

def z973 : W := mkw 0xdbff0001ef780000 0x436ffc0007bde000 0xfff30001fffc0006 0xebffcc0007fff000

def z974 : W := mkw 0x011504abdfefffee 0x24045412af7fbfff 0x00000001ffffffc0 0x8c00000007ffffff

def z975 : W := mkw 0xdbff0355ef780000 0x536ffc0d57bde000 0xffff0381fffc001f 0xebfffc0e07fff000

def z976 : W := mkw 0x0115042b8c6036ea 0x00045410ae3180db 0x033f3c7f80607ff4 0x140cfcf1fe0181ff

def z977 : W := mkw 0x0c4c519805ad8b4c 0x043131466016b62d 0x1cccf3998fffffff 0xbc7333ce663fffff

def z978 : W := mkw 0xdaee000067380000 0x436bb800019ce000 0xfccc00007f9c000a 0x6bf3300001fe7000

def z979 : W := mkw 0x60b0a2e0b056d1b0 0x0982c28b82c15b46 0xe0f0f3e1fc7fffff 0xdf83c3cf87f1ffff

def z980 : W := mkw 0xfeeafb5452024000 0x33fbabed51480900 0xfffffffe7000003f 0x73fffffff9c00000

def z981 : W := mkw 0x60b0a080b056c100 0x0182c28202c15b04 0xe0f0e381f07ff1f7 0xdf83c38e07c1ffc7

def z982 : W := mkw 0xdbff0401ef782400 0x436ffc1007bde090 0xffff2c01fffc701f 0xebfffcb007fff1c0

def z983 : W := mkw 0x2400fae01087d9b0 0x289003eb80421f66 0x0000e3e00003f1e0 0x1400038f80000fc7

def z984 : W := mkw 0x930004015a836c00 0x224c0010056a0db0 0xfc000001ff83fe02 0xeff0000007fe0ff8

def z985 : W := mkw 0xb700fc015a836c00 0x22dc03f0056a0db0 0xff00dc01ff83fe0a 0xeffc037007fe0ff8

def z986 : W := mkw 0xfeeafb5400000000 0x13fbabed50000000 0xfffffffe0c000e3f 0xf7fffffff8300038

def z987 : W := mkw 0xb702fc055a836c00 0x32dc0bf0156a0db0 0xff03fc07ff83fe2f 0xeffc0ff01ffe0ff8

def z988 : W := mkw 0x2c48fb5400000000 0x10b123ed50000000 0x1ffffffe0000003f 0x307ffffff8000000

def z989 : W := mkw 0xdbff040bef78264a 0x436ffc102fbde099 0xffff0001fffc0e1f 0xebfffc0007fff038

def z990 : W := mkw 0xfeeafb5400000000 0x13fbabed50000000 0xfffffffe007c003f 0xfbfffffff801f000

def z991 : W := mkw 0x2010a0a0b056d1b0 0x0880428282c15b46 0xe0c0e381f07ff1f7 0xdf83038e07c1ffc7

def z992 : W := mkw 0x0000035400000000 0x1000000d50000000 0x033f3ffe0000003d 0x100cfcfff8000000

def z993 : W := mkw 0x2500f40118836c00 0x009403d004620db0 0xff00fc01ff83fe2f 0xeffc03f007fe0ff8

def z994 : W := mkw 0x48f80000a1580000 0x0123e00002856000 0xfcf00001f3fc0017 0xebf3c00007cff000

def z995 : W := mkw 0xfeeafb5410834800 0x13fbabed50420d20 0xffffffffff83fe3f 0xfffffffffffe0ff8

def z996 : W := mkw 0xdbff0423ef7834a2 0x436ffc108fbde0d2 0xffff2c67fffc71ff 0xfffffcb19ffff1c7

def z997 : W := mkw 0x0848011000000000 0x0021200440000000 0x03ff3ffe0000003d 0x100ffcfff8000000

def z998 : W := mkw 0xdafa0000e3580000 0x436be800038d6000 0xfcf00001f39c0006 0x6bf3c00007ce7000

def z999 : W := mkw 0xdbff002bef7812ea 0x436ffc00afbde04b 0xffff0001fffc01df 0xebfffc0007fff007

def z1000 : W := mkw 0x2515f7fb9ce7fffe 0x0c9457dfee739fff 0x033fffff8c63fffd 0x940cfffffe318fff

def z1001 : W := mkw 0xdbff0023ef7810a2 0x436ffc008fbde042 0xffff0067fffc001f 0xebfffc019ffff000

def z1002 : W := mkw 0x48ea035400000000 0x1123a80d50000000 0x03ff1ffe00000018 0x100ffc7ff8000000

def z1003 : W := mkw 0x0115042b8c6036ea 0x00045410ae3180db 0x033f3c7f8c607fdc 0x100cfcf1fe3181ff

def z1004 : W := mkw 0x2400fc881087ef4c 0x249003f220421fbd 0x0000fc000003ffe0 0x040003f000000fff

def z1005 : W := mkw 0xdbff0421ef7834a0 0x436ffc1087bde0d2 0xffff3c61fffc7fff 0xfffffcf187fff1ff

def z1006 : W := mkw 0x60b0a2e0b056d1b0 0x0982c28b82c15b46 0xe0f0e3e1f07ff1f4 0x5783c38f87c1ffc7

def z1007 : W := mkw 0xdbff0001ef780000 0x436ffc0007bde000 0xffff0001ff9c000e 0x6bfffc0007fe7000

def z1008 : W := mkw 0xdbff037fef7812ea 0x536ffc0dffbde04b 0xffff03fffffc01df 0xfbfffc0ffffff007

def z1009 : W := mkw 0xdbee00016f380000 0x436fb80005bce000 0xffcc0001fffc001f 0xebff300007fff000

def z1010 : W := mkw 0x60b0a2e0b056d1b0 0x0982c28b82c15b46 0xe0c0c381f07ff1f3 0xdf83030e07c1ffc7

def z1011 : W := mkw 0xdbff0001ef780000 0x436ffc0007bde000 0xffff1c1ffffc001f 0xebfffc707ffff000

def z1012 : W := mkw 0xfeeafb5400810800 0x13fbabed50020420 0xfffffffe00038e3f 0x77fffffff8000e38

def z1013 : W := mkw 0xdbef040b6f38264a 0x436fbc102dbce099 0xffcf1c1e7f9c0e0a 0x6bff3c7079fe7038

def z1014 : W := mkw 0xdaea0b5400000000 0x136ba82d50000000 0x03ff0ffe00000010 0x100ffc3ff8000000

def z1015 : W := mkw 0xfeeafb5400000000 0x13fbabed50000000 0xffffeffe00000016 0x73ffffbff8000000

def z1016 : W := mkw 0xfaeaab5400000000 0x13ebaaad50000000 0xe3ff3ffe0000003d 0x538ffcfff8000000

def z1017 : W := mkw 0xdaff0000e7780000 0x436bfc00039de000 0xffff000073fc001f 0x6bfffc0001cff000

def z1018 : W := mkw 0xdbff0001ef780000 0x436ffc0007bde000 0xffc00001fffc000f 0xebff000007fff000

def z1019 : W := mkw 0xdbeb00016b180000 0x436fac0005ac6000 0xffc30000739c0002 0x6bff0c0001ce7000

def z1020 : W := mkw 0xdaee000067380000 0x436bb800019ce000 0xfccc000073fc0012 0x6bf3300001cff000

def z1021 : W := mkw 0xdbff0119ef78024c 0x476ffc0467bde009 0xffff0019fffc001f 0xebfffc0067fff000

def z1022 : W := mkw 0xdaef000067380000 0x436bbc00019ce000 0xfccf0000739c0002 0x6bf33c0001ce7000

def z1023 : W := mkw 0xdbff0001ef780000 0x436ffc0007bde000 0xffff00007ffc001a 0x6bfffc0001fff000

def z1024 : W := mkw 0x0105042b0c2036ea 0x00041410ac3080db 0x033f3c7e0c007ffd 0x140cfcf1f83001ff

def z1025 : W := mkw 0xdaee000067380000 0x436bb800019ce000 0xffff00007ffc001f 0xebfffc0001fff000

def z1026 : W := mkw 0x0400519800858b4c 0x041001466002162d 0x1cc0d3980fff8ffb 0xbc73034e603ffe3f

def z1027 : W := mkw 0x49fd0001ad780000 0x0127f40006b5e000 0xffff0001fffc001f 0xebfffc0007fff000

def z1028 : W := mkw 0xb600f80010834800 0x02d803e000420d20 0xff00fc01ff83fe2f 0xeffc03f007fe0ff8

def z1029 : W := mkw 0x9a4c000047280000 0x02693000011ca000 0xfccc00007ffc001b 0xebf3300001fff000

def z1030 : W := mkw 0x0115042b8c6036ea 0x00045410ae3180db 0x033f3c7e0c607ff8 0x140cfcf1f83181ff

def z1031 : W := mkw 0x0100042b080036ea 0x00040010ac2000db 0x033f3c7f8c007ffd 0x940cfcf1fe3001ff

def z1032 : W := mkw 0x2400fc801087ed00 0x209003f200421fb4 0x0000ff800003ffe0 0x140003fe00000fff

def z1033 : W := mkw 0x0c4c519805ad8b4c 0x043131466016b62d 0x1cc0d3980fff8fe2 0xbc73034e603ffe3f

def z1034 : W := mkw 0x0115042b8c6036ea 0x00045410ae3180db 0xe33f3c7ffc607fff 0xdf8cfcf1fff181ff

def z1035 : W := mkw 0x9b4800014b080000 0x026d2000052c2000 0xffc00001ff9c000f 0xebff000007fe7000

def z1036 : W := mkw 0x2400f9981087cb4c 0x249003e660421f2d 0x0000d39800038fe0 0x1400034e60000e3f

def z1037 : W := mkw 0xb700fc015a836c00 0x22dc03f0056a0db0 0xffc0fc01fffffe3f 0xefff03f007fffff8

def z1038 : W := mkw 0xdbff042bef7836ea 0x436ffc10afbde0db 0xffff2061fffc7fff 0xfffffc8187fff1ff

def z1039 : W := mkw 0x0c4d519a05ad8b4e 0x043135466816b62d 0x1ccfd39e0fff8ffb 0xbc733f4e783ffe3f

def z1040 : W := mkw 0x2400fdba1087ffee 0x249003f6e8421fff 0x0000fffe0003ffe0 0x140003fff8000fff

def z1041 : W := mkw 0xdbff0001ef780000 0x436ffc0007bde000 0xffff0001fffc001c 0x63fffc0007fff000

def z1042 : W := mkw 0xdbff042bef7836ea 0x436ffc10afbde0db 0xffff3c7ffffc7e1f 0xebfffcf1fffff1f8

def z1043 : W := mkw 0x49fd042bad7836ea 0x0127f410aeb5e0db 0xffff3c7ffffc7fff 0xfffffcf1fffff1ff

def z1044 : W := mkw 0xdbff000bef78024a 0x436ffc002fbde009 0xffff001ffffc001f 0xebfffc007ffff000

def z1045 : W := mkw 0xfeeafb5400000000 0x13fbabed50000000 0xfffffffe0003803f 0xfffffffff8000e00

def z1046 : W := mkw 0x0c48519000858900 0x0031214640021624 0x1cccd3980fff8ffb 0xbc73334e603ffe3f

def z1047 : W := mkw 0xdafa0000e3580000 0x436be800038d6000 0xfcc00001f3fc0002 0xebf3000007cff000

def z1048 : W := mkw 0xdbff0409ef782648 0x436ffc1027bde099 0xffff3c19fffc7fff 0xfffffcf067fff1ff

def z1049 : W := mkw 0xfeeafb5400000000 0x13fbabed50000000 0xffffffff8000703f 0xf7fffffffe0001c0

def z1050 : W := mkw 0x2400fec01087ed10 0x289003fb00421fb4 0x0000ff800003fe20 0x040003fe00000ff8

def z1051 : W := mkw 0xdbff0401ef782400 0x436ffc1007bde090 0xffff3c7ffffc7e3f 0xfffffcf1fffff1f8

def z1052 : W := mkw 0xdbff0009ef780248 0x436ffc0027bde009 0xffff1019fffc0e1f 0xebfffc4067fff038

def z1053 : W := mkw 0x930000016b180000 0x424c000005ac6000 0xff000001ff9c000f 0xebfc000007fe7000

def z1054 : W := mkw 0x6ce8f35000000000 0x01b3a3cd40000000 0xfffffffe0000003f 0x73fffffff8000000

def z1055 : W := mkw 0x0c4c599c05ad8b4c 0x143131667016b62d 0x1cccdf9e0fff8ffb 0xbc73337e783ffe3f

def z1056 : W := mkw 0x48fe03fca57c93fc 0x1d23f80ff295f24f 0x00ff03fe007c01d0 0x1003fc0ff801f007

def z1057 : W := mkw 0xfeeafb5400000000 0x13fbabed50000000 0xfffffffe0f80003f 0xfbfffffff83e0000

def z1058 : W := mkw 0x0115042bad7836ea 0x40045410aeb5e0db 0x033f3c7f8c7c7ffd 0x940cfcf1fe31f1ff

def z1059 : W := mkw 0xfeeafb5452834800 0x33fbabed514a0d20 0xfffffffe7f838e3f 0xfffffffff9fe0e38

def z1060 : W := mkw 0xb701fc035a836c02 0x22dc07f00d6a0db0 0xff03fc07ff83fe2f 0xeffc0ff01ffe0ff8

def z1061 : W := mkw 0x0c4c508005ad8900 0x003131420016b624 0x1cccd3800fff8ffb 0xbc73334e003ffe3f

def z1062 : W := mkw 0x68eaa35400000000 0x11a3aa8d50000000 0xe3fffffe0000003f 0x538ffffff8000000

def z1063 : W := mkw 0x0115042b8c6036ea 0x00045410ae3180db 0x033f3c7f8c607fcc 0x840cfcf1fe3181ff

def z1064 : W := mkw 0xdbff002bef7812ea 0x436ffc00afbde04b 0xffff107ffffc0fff 0xfffffc41fffff03f

def z1065 : W := mkw 0x0111042b884036ea 0x00044410ae2100db 0x033f3c7f80007ffd 0x140cfcf1fe0001ff

def z1066 : W := mkw 0xd3b5042bee7036ea 0x034ed410afb9c0db 0xffff3c7ffffc7fff 0xfffffcf1fffff1ff

def z1067 : W := mkw 0x0115042bce6036ea 0x00045410af3980db 0x033f3c7fffe07ffd 0x9c0cfcf1ffff81ff

def z1068 : W := mkw 0xfeeafb5400000000 0x13fbabed50000000 0xfffffffe0000000e 0x63fffffff8000000

def z1069 : W := mkw 0xdeea5b5400000000 0x137ba96d50000000 0x1fff3ffe0000003d 0x307ffcfff8000000

def z1070 : W := mkw 0x48e8000021180000 0x0123a00000846000 0xfcc00000739c0002 0x6bf3000001ce7000

def z1071 : W := mkw 0xdaff002ae77812ea 0x436bfc00ab9de04b 0xfcff007e73fc01d2 0x7bf3fc01f9cff007

def z1072 : W := mkw 0x9f4e5d1d4fa92e4c 0x367d3974753ea4b9 0x1f0f1c1e0f800e08 0x207c3c70783e0038

def z1073 : W := mkw 0x60b0a2e0b056d1b0 0x0982c28b82c15b46 0xe3f0ffe1f07ff1ff 0xdf8fc3ff87c1ffc7

def z1074 : W := mkw 0x60b0a2e0b056d1b0 0x0982c28b82c15b46 0xe0f0c3e1f07ff1d2 0xdf83c30f87c1ffc7

def z1075 : W := mkw 0x2400ffdc1087ef4c 0x349003ff70421fbd 0x0000fffe0003ffe0 0x140003fff8000fff

def z1076 : W := mkw 0xdeea5b5400000000 0x137ba96d50000000 0x1fffdffe0000003b 0x307fff7ff8000000

def z1077 : W := mkw 0x2400f1981087cb4c 0x049003c660421f2d 0x0000f3980003ffe0 0x140003ce60000fff

def z1078 : W := mkw 0xdbef00016f380000 0x436fbc0005bce000 0xfcc000007f9c0002 0x6bf3000001fe7000

def z1079 : W := mkw 0x4cea535400000000 0x1133a94d50000000 0x1ffffffe0000003f 0x307ffffff8000000

def z1080 : W := mkw 0xb700fc015a836c00 0x22dc03f0056a0db0 0xff00c001ff83fe0f 0xeffc030007fe0ff8

def z1081 : W := mkw 0x970054015a836c00 0x225c0150056a0db0 0xff00d001ff83fe2f 0xeffc034007fe0ff8

def z1082 : W := mkw 0xfeeafb5400810800 0x13fbabed50020420 0xfffffffe0383803f 0x7bfffffff80e0e00

def z1083 : W := mkw 0xb700fc015a836c00 0x22dc03f0056a0db0 0xff0ffc1fff83fe2f 0xeffc3ff07ffe0ff8

def z1084 : W := mkw 0xdbfb0001eb580000 0x436fec0007ad6000 0xfcc00001f39c0002 0x6bf3000007ce7000

def z1085 : W := mkw 0xdaea000063180000 0x436ba800018c6000 0xfcc00001f39c0007 0xebf3000007ce7000

def z1086 : W := mkw 0x0c4c519805ad8b4c 0x043131466016b62d 0x1cfcf3f80fff8fff 0xbc73f3cfe03ffe3f

def z1087 : W := mkw 0x60b0a2e0b056d1b0 0x0982c28b82c15b46 0xe3f3efe7f07ff1f7 0xdf8fcfbf9fc1ffc7

def z1088 : W := mkw 0xdbfa0001eb580000 0x436fe80007ad6000 0xfff00001fffc001f 0xebffc00007fff000

def z1089 : W := mkw 0xdbff0001ef780000 0x436ffc0007bde000 0xffff0001fffc01ff 0xfffffc0007fff007

def z1090 : W := mkw 0xfeeafb5401890804 0x17fbabed50062420 0xfffffffe0380003f 0x73fffffff80e0000

def z1091 : W := mkw 0xfaeaab5400000000 0x13ebaaad50000000 0xffff2ffe0000001f 0x73fffcbff8000000

def z1092 : W := mkw 0x0c4c519805ad8b4c 0x043131466016b62d 0x1cc0c3800fff8ff3 0xbc73030e003ffe3f

def z1093 : W := mkw 0x0c4c519805ad8b4c 0x043131466016b62d 0x1fccff980fff8fff 0xbc7f33fe603ffe3f

def z1094 : W := mkw 0xdafe0000e7780000 0x436bf800039de000 0xfcfc0001fffc001f 0xebf3f00007fff000

def z1095 : W := mkw 0xdbef00016f380000 0x436fbc0005bce000 0xffcf0001ff9c000f 0xebff3c0007fe7000

def z1096 : W := mkw 0x48ff03f8a57c93fc 0x4d23fc0fe295f24f 0x00ff03f8007c01d0 0x1003fc0fe001f007

def z1097 : W := mkw 0xdbff002bef7812ea 0x436ffc00afbde04b 0xffff207ffffc71ff 0xfffffc81fffff1c7

def z1098 : W := mkw 0xdbea00016b180000 0x436fa80005ac6000 0xfcc00001ff9c0002 0xebf3000007fe7000

def z1099 : W := mkw 0xdbff040bef78264a 0x436ffc102fbde099 0xffff1c1ffffc0fff 0xfffffc707ffff03f

def z1100 : W := mkw 0x48ec000025380000 0x0123b0000094e000 0xfccc00007ffc001b 0xebf3300001fff000

def z1101 : W := mkw 0xdbea04016b182400 0x436fa81005ac6090 0xffc03c01ff9c7e2f 0xefff00f007fe71f8

def z1102 : W := mkw 0xdbee00014f280000 0x036fb800053ca000 0xffff0001fffc001f 0xebfffc0007fff000

def z1103 : W := mkw 0xdbff0009ef780248 0x436ffc0027bde009 0xffff3c7ffffc0fff 0xfffffcf1fffff03f

def z1104 : W := mkw 0xdbff0001ef780000 0x436ffc0007bde000 0xffff2061fffc003f 0xfbfffc8187fff000

def z1105 : W := mkw 0xfeeafb5442810800 0x33fbabed510a0420 0xfffffffe0380003f 0x73fffffff80e0000

def z1106 : W := mkw 0x084c000005280000 0x002130000014a000 0xfccc0001fffc001f 0xebf3300007fff000

def z1107 : W := mkw 0xdafe0000a5780000 0x036bf8000295e000 0xffff0001fffc001f 0xebfffc0007fff000

def z1108 : W := mkw 0x2500f4015a836c00 0x209403d0056a0db0 0xfc00f001ff83fe2f 0xeff003c007fe0ff8

def z1109 : W := mkw 0xdbff0245ef780000 0x536ffc0917bde000 0xffff0067fffc001f 0xebfffc019ffff000

def z1110 : W := mkw 0x011504ab8d6cb7ee 0x04045412ae35b2df 0x000000018c7c7fc0 0x840000000631f1ff

def z1111 : W := mkw 0x9b4c04094f282648 0x026d3010253ca099 0xffcc3c19fffc7fff 0xffff30f067fff1ff

def z1112 : W := mkw 0xdbff042bef7836ea 0x436ffc10afbde0db 0xffff1019fffc7fff 0xfffffc4067fff1ff

def z1113 : W := mkw 0xdafa0000e3580000 0x436be800038d6000 0xfcf0000073fc0012 0x6bf3c00001cff000

def z1114 : W := mkw 0x60b1a2e2b056d1b2 0x0982c68b8ac15b46 0xe0f3e3e7f07ff1f7 0xdf83cf8f9fc1ffc7

def z1115 : W := mkw 0xdaea035463180000 0x536ba80d518c6000 0xfcff03fe739c0012 0x7bf3fc0ff9ce7000

def z1116 : W := mkw 0xdbff0029ef7812e8 0x436ffc00a7bde04b 0xffff3079fffc7fff 0xfffffcc1e7fff1ff

def z1117 : W := mkw 0xdafb0000e3580000 0x436bec00038d6000 0xfcf30000739c0002 0x6bf3cc0001ce7000

def z1118 : W := mkw 0xdbff0115ef780000 0x536ffc0457bde000 0xffff001ffffc001f 0xebfffc007ffff000

def z1119 : W := mkw 0x9f4f5d194fa92e4c 0x667d3d74653ea4b9 0x1f0f1c180f800e08 0x207c3c70603e0038

def z1120 : W := mkw 0x2400f3d01087c914 0x0c9003cf40421f24 0x0000c38000038000 0x0000030e00000e00

def z1121 : W := mkw 0xd3b00421ea5034a0 0x034ec01087a940d2 0xfff03c61fffc7fff 0xffffc0f187fff1ff

def z1122 : W := mkw 0xdbff0001ef780000 0x436ffc0007bde000 0xff3f0001fffc000c 0xebfcfc0007fff000

def z1123 : W := mkw 0x93100001ea500000 0x024c400007a94000 0xff000001fffc000f 0xebfc000007fff000

def z1124 : W := mkw 0xf3b3ae61fa5274b0 0x6bceceb987e949d2 0xe3332c61f0007004 0x438cccb187c001c0

def z1125 : W := mkw 0x0c4e519c05ad8b4c 0x143139467016b62d 0x1ccfd39e0fff8ffb 0xbc733f4e783ffe3f

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6])],[(0,[z7,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z8,z9,z6]),(0,[z10,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z11,z5,z6]),(0,[z1,z2,z3,z12,z4,z5,z6]),(0,[z1,z13,z2,z3,z4,z5,z6]),(0,[z1,z2,z14,z3,z4,z6,z15])],[(0,[z1,z2,z16,z3,z4,z5,z6]),(0,[z17,z1,z18,z3,z4,z5,z6]),(0,[z1,z2,z3,z19,z4,z20,z6]),(0,[z1,z2,z3,z4,z5,z21,z6]),(0,[z1,z22,z2,z3,z4,z5,z6]),(0,[z23,z1,z2,z3,z4,z5,z6])],[(0,[z24,z1,z2,z3,z4,z5,z6]),(0,[z25,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z26,z4,z6]),(0,[z1,z2,z3,z4,z27,z6,z28])],[(0,[z1,z2,z29,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z8,z6]),(0,[z30,z1,z2,z31,z4,z5,z6]),(0,[z1,z2,z3,z32,z4,z5,z6])],[(0,[z33,z1,z18,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z34,z6]),(0,[z1,z2,z3,z4,z35,z5,z6]),(0,[z1,z36,z2,z3,z4,z20,z6]),(1,[z30,z1,z37,z4,z5,z6]),(0,[z38,z1,z2,z3,z4,z5,z6]),(0,[z1,z39,z2,z3,z4,z5,z6]),(0,[z1,z2,z40,z3,z4,z5,z6]),(0,[z1,z2,z41,z3,z42,z4,z6])],[(0,[z1,z2,z3,z43,z4,z5,z6]),(0,[z1,z44,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z45,z4,z20,z6]),(0,[z46,z1,z2,z47,z3,z4,z5]),(0,[z1,z48,z2,z49,z3,z4,z6])],[(0,[z1,z2,z3,z4,z50,z5,z6]),(0,[z1,z2,z51,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z52,z4,z5,z6]),(0,[z2,z3,z53,z4,z54,z5,z6]),(0,[z1,z48,z2,z3,z4,z55,z6]),(0,[z33,z1,z2,z3,z4,z5,z56]),(0,[z1,z2,z3,z4,z5,z6,z57])],[(0,[z58,z2,z18,z3,z4,z5,z6]),(0,[z59,z1,z2,z3,z4,z5,z6]),(1,[z60,z2,z3,z4,z8,z6]),(0,[z1,z61,z2,z41,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z62,z6]),(0,[z1,z2,z63,z3,z64,z5,z6]),(0,[z1,z2,z41,z3,z4,z65,z6])],[(0,[z66,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z67,z6]),(0,[z1,z2,z68,z3,z4,z5,z69])],[(0,[z1,z70,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z71,z6]),(0,[z1,z2,z3,z72,z4,z5,z6]),(0,[z1,z73,z2,z3,z4,z8,z6]),(0,[z1,z2,z74,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z75]),(0,[z1,z2,z3,z4,z5,z6,z76])],[(0,[z1,z2,z3,z4,z5,z77,z6]),(0,[z1,z2,z3,z78,z4,z5,z6]),(0,[z1,z2,z79,z3,z4,z20,z5]),(1,[z1,z39,z3,z4,z5,z76]),(0,[z1,z2,z3,z80,z4,z5,z6])],[(0,[z81,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z82,z5,z6]),(0,[z1,z2,z83,z3,z4,z5,z6])]],
   [[(1,[z84,z2,z85,z4,z5,z6]),(0,[z86,z1,z2,z87,z3,z4,z5])],[(0,[z1,z2,z3,z53,z4,z20,z6]),(0,[z86,z1,z2,z3,z53,z5,z6]),(0,[z60,z1,z2,z3,z4,z5,z6]),(0,[z1,z88,z2,z3,z4,z8,z6]),(0,[z1,z2,z89,z4,z90,z5,z6]),(0,[z1,z2,z91,z3,z4,z5,z6]),(0,[z1,z2,z3,z92,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z93]),(0,[z94,z1,z2,z3,z4,z5,z6]),(0,[z1,z39,z2,z3,z4,z5,z56]),(1,[z1,z2,z3,z92,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z95]),(0,[z1,z2,z3,z96,z4,z5,z6]),(1,[z97,z2,z3,z4,z8,z6]),(0,[z1,z2,z47,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z5,z6,z98])],[(0,[z46,z1,z2,z3,z4,z5,z28]),(0,[z1,z99,z2,z3,z100,z5,z6]),(0,[z1,z101,z2,z3,z4,z5,z6])],[(0,[z1,z102,z2,z3,z4,z5,z6]),(0,[z103,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z55,z6])],[(0,[z1,z104,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z105,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z106,z6]),(0,[z84,z1,z2,z3,z4,z5,z6]),(1,[z107,z2,z3,z53,z5,z6]),(0,[z1,z108,z2,z3,z4,z5,z6]),(0,[z1,z2,z109,z3,z4,z5,z6]),(0,[z110,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z111,z4,z6,z15]),(0,[z1,z2,z3,z4,z5,z6,z112])]],
   [[(0,[z113,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z114,z6]),(1,[z1,z2,z3,z4,z115,z6]),(0,[z116,z1,z2,z3,z4,z115,z6]),(0,[z1,z2,z49,z14,z3,z4,z6]),(0,[z1,z2,z117,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z118,z6]),(0,[z1,z2,z3,z119,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z120,z6])],[(0,[z81,z1,z2,z3,z4,z121,z6]),(0,[z1,z2,z3,z4,z20,z6,z122]),(0,[z30,z1,z2,z123,z4,z5,z6]),(1,[z1,z2,z124,z3,z4,z6]),(0,[z125,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z126]),(0,[z127,z1,z2,z68,z4,z5,z6]),(0,[z1,z2,z3,z4,z27,z5,z6])],[(0,[z1,z2,z128,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z54,z20,z6]),(0,[z1,z2,z129,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z130,z9,z6]),(0,[z1,z2,z3,z4,z5,z131,z6])],[(0,[z132,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z133,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z6]),(0,[z30,z1,z3,z37,z4,z5,z6]),(0,[z1,z2,z3,z4,z134,z5,z6]),(0,[z1,z2,z135,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z136,z5,z6])],[(0,[z1,z2,z3,z100,z4,z8,z6]),(0,[z1,z2,z3,z4,z137,z5,z6]),(0,[z97,z1,z2,z3,z138,z5,z6]),(0,[z127,z46,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z139,z6]),(0,[z1,z2,z87,z3,z4,z5,z56]),(0,[z1,z2,z3,z4,z140,z5,z6]),(0,[z1,z141,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z142,z4,z5,z6]),(0,[z116,z1,z2,z3,z4,z5,z6]),(0,[z1,z61,z2,z3,z111,z4,z6]),(0,[z143,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z144,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z6,z145]),(0,[z1,z146,z2,z3,z4,z8,z6]),(0,[z1,z2,z147,z3,z37,z5,z6]),(0,[z1,z2,z148,z3,z4,z5,z6])],[(0,[z149,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z150,z4,z5,z6])],[(0,[z1,z2,z151,z3,z4,z5,z6]),(0,[z1,z2,z152,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z153,z5,z6]),(0,[z1,z2,z3,z4,z154,z5,z6]),(0,[z1,z2,z155,z3,z4,z5,z6])],[(0,[z156,z1,z2,z3,z4,z5,z6]),(0,[z46,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z5,z6,z157]),(0,[z1,z2,z3,z4,z158,z9,z6]),(1,[z1,z2,z3,z19,z5,z159]),(0,[z1,z2,z3,z4,z5,z6,z160]),(0,[z1,z2,z3,z4,z5,z6,z161])],[(0,[z1,z2,z3,z4,z5,z162,z6]),(0,[z97,z1,z2,z3,z4,z20,z6]),(0,[z1,z2,z63,z3,z4,z5,z6]),(0,[z1,z2,z3,z163,z4,z5,z6]),(1,[z164,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z165,z6]),(0,[z1,z2,z3,z4,z4,z5,z6]),(0,[z1,z166,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z167,z6]),(0,[z1,z2,z64,z4,z5,z9,z6]),(0,[z1,z2,z168,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z169]),(0,[z84,z1,z2,z85,z4,z5,z6]),(0,[z1,z2,z170,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z20,z171,z6]),(0,[z1,z2,z3,z4,z20,z21,z6]),(1,[z1,z2,z172,z3,z4,z6]),(0,[z1,z2,z3,z173,z4,z5,z6]),(0,[z1,z2,z3,z4,z174,z5,z6])],[(0,[z1,z175,z2,z3,z4,z5,z6]),(0,[z1,z2,z176,z3,z4,z5,z6]),(0,[z107,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z8,z56,z6]),(0,[z1,z2,z14,z3,z4,z8,z6]),(0,[z1,z2,z68,z3,z4,z20,z6]),(0,[z1,z2,z3,z177,z4,z5,z6]),(0,[z1,z178,z2,z3,z4,z5,z6]),(0,[z1,z2,z179,z3,z4,z5,z6]),(0,[z1,z2,z49,z3,z4,z5,z6])]],
   [[(0,[z180,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z20,z8,z6]),(0,[z1,z181,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z5,z182,z6])],[(0,[z183,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z184,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z185,z6])],[(0,[z1,z2,z186,z3,z4,z5,z6]),(0,[z1,z2,z187,z3,z4,z20,z6]),(1,[z1,z2,z3,z4,z121,z6]),(0,[z188,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z8,z6,z189]),(0,[z1,z2,z3,z190,z4,z5,z6]),(0,[z191,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z123,z3,z64,z5,z6]),(0,[z1,z192,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z193,z5,z6]),(0,[z1,z2,z194,z3,z4,z5,z6])],[(0,[z1,z2,z41,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z28]),(0,[z195,z1,z2,z3,z4,z5,z6]),(1,[z1,z73,z3,z100,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z196]),(0,[z1,z2,z3,z4,z197,z5,z6]),(0,[z1,z2,z198,z3,z4,z5,z6])],[(0,[z1,z99,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z199,z5,z6]),(0,[z1,z2,z200,z3,z4,z5,z6]),(0,[z1,z2,z3,z201,z4,z5,z6]),(0,[z46,z1,z2,z3,z4,z5,z159]),(0,[z1,z2,z3,z4,z5,z6,z202]),(0,[z1,z2,z203,z3,z4,z5,z6]),(0,[z204,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z205,z3,z37,z5,z6]),(0,[z1,z2,z3,z206,z4,z5,z6]),(1,[z33,z1,z3,z4,z5,z56]),(0,[z1,z2,z87,z3,z19,z4,z5])],[(0,[z1,z2,z3,z4,z5,z6,z207]),(0,[z1,z2,z208,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z158,z6]),(0,[z1,z209,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z210,z6]),(0,[z1,z2,z211,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z212,z6]),(0,[z1,z2,z213,z3,z4,z5,z6]),(0,[z1,z2,z214,z3,z4,z20,z6]),(0,[z1,z61,z2,z3,z4,z20,z6]),(0,[z1,z215,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z216,z4,z5,z6]),(0,[z1,z2,z3,z4,z20,z6,z76]),(0,[z97,z46,z2,z3,z4,z5,z6]),(0,[z1,z2,z123,z4,z5,z9,z6]),(0,[z1,z2,z14,z41,z3,z4,z6])],[(0,[z1,z2,z3,z4,z35,z8,z6]),(1,[z1,z2,z3,z4,z5,z217])],[(0,[z1,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z218,z6]),(0,[z1,z219,z2,z3,z4,z5,z6]),(0,[z1,z61,z3,z4,z220,z5,z6])],[(0,[z1,z221,z2,z18,z3,z4,z5]),(0,[z107,z1,z2,z3,z53,z5,z6]),(1,[z1,z222,z3,z4,z5,z6]),(0,[z1,z223,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z224,z4,z5,z6])],[(0,[z225,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z226]),(0,[z227,z1,z2,z3,z4,z5,z6]),(0,[z228,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z229,z5,z6]),(0,[z230,z1,z2,z3,z4,z5,z6])],[(0,[z231,z1,z2,z3,z4,z5,z6]),(0,[z232,z2,z3,z4,z5,z171,z6]),(0,[z233,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z234,z3,z4,z5,z6]),(0,[z1,z2,z235,z3,z4,z5,z6]),(0,[z1,z2,z41,z4,z5,z65,z6])]],
   [[(0,[z1,z2,z236,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z237,z5,z6]),(0,[z1,z2,z3,z4,z5,z238,z6]),(0,[z1,z2,z3,z4,z5,z239,z6]),(0,[z1,z2,z240,z3,z4,z5,z6])],[(0,[z1,z2,z3,z241,z4,z5,z6]),(0,[z242,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z122]),(1,[z1,z2,z147,z3,z5,z6]),(0,[z1,z2,z3,z243,z4,z5,z6]),(0,[z244,z1,z2,z3,z4,z5,z6])],[(0,[z1,z48,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z245,z4,z5,z6]),(0,[z1,z2,z246,z3,z4,z5,z6])],[(0,[z107,z1,z2,z3,z4,z247,z6]),(0,[z1,z248,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z27,z28])],[(0,[z1,z2,z3,z249,z4,z5,z6]),(0,[z81,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z5,z250,z6]),(0,[z1,z2,z124,z3,z37,z4,z6]),(0,[z1,z2,z251,z3,z4,z5,z6]),(0,[z252,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z253,z3,z4,z5,z6]),(0,[z1,z2,z123,z63,z4,z5,z6])],[(0,[z254,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z111,z4,z8,z6]),(0,[z1,z73,z2,z3,z4,z20,z6]),(0,[z1,z2,z3,z4,z255,z5,z6]),(0,[z1,z2,z3,z256,z4,z5,z6]),(0,[z1,z31,z3,z100,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z257]),(0,[z1,z2,z3,z4,z5,z258,z6]),(0,[z1,z2,z259,z3,z4,z5,z6])],[(0,[z58,z1,z2,z3,z4,z5,z6]),(0,[z84,z1,z2,z3,z4,z260,z6]),(0,[z60,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z87,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z5,z261,z6]),(1,[z1,z2,z63,z64,z5,z6]),(0,[z1,z2,z3,z111,z5,z6,z159])],[(0,[z1,z221,z2,z3,z4,z5,z6]),(0,[z1,z146,z2,z37,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z262,z6]),(0,[z1,z2,z3,z4,z5,z76,z159])]],
   [[(0,[z1,z2,z3,z4,z263,z5,z6]),(0,[z97,z1,z2,z3,z4,z5,z159]),(0,[z1,z2,z31,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z264]),(0,[z1,z2,z265,z3,z4,z5,z6])],[(0,[z1,z266,z2,z3,z4,z5,z6]),(0,[z1,z2,z79,z3,z4,z5,z6]),(0,[z46,z1,z2,z3,z4,z267,z6]),(0,[z1,z2,z268,z3,z4,z5,z6])],[(0,[z1,z2,z3,z269,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z270]),(0,[z271,z1,z2,z3,z4,z5,z6]),(0,[z272,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z89,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z273,z6])],[(0,[z1,z274,z2,z3,z4,z5,z6]),(0,[z275,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z276,z3,z4,z5,z6]),(1,[z1,z2,z79,z3,z4,z5]),(0,[z1,z2,z3,z277,z4,z5,z6])],[(0,[z1,z2,z47,z3,z4,z20,z6]),(0,[z1,z48,z2,z41,z3,z4,z6]),(0,[z278,z1,z2,z3,z4,z5,z6]),(0,[z279,z1,z2,z3,z4,z5,z6]),(0,[z280,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z49,z42,z4,z6]),(0,[z1,z2,z14,z198,z3,z5,z6]),(0,[z1,z2,z281,z3,z4,z5,z6])],[(0,[z1,z2,z3,z282,z4,z5,z6]),(0,[z1,z2,z3,z4,z8,z6,z159]),(0,[z1,z2,z3,z4,z5,z171,z6]),(0,[z1,z2,z123,z3,z4,z5,z6]),(0,[z283,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z47,z3,z284,z5,z6])],[(1,[z1,z2,z3,z4,z260,z6]),(1,[z1,z129,z3,z4,z5,z6]),(0,[z1,z2,z3,z285,z4,z5,z6]),(0,[z1,z73,z2,z3,z90,z5,z6]),(0,[z1,z2,z3,z286,z4,z5,z6])],[(0,[z287,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z27,z8,z6]),(0,[z86,z1,z2,z3,z4,z5,z6]),(0,[z149,z1,z2,z47,z3,z4,z5])]],
   [[(0,[z30,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z124,z3,z4,z5,z6]),(1,[z1,z2,z40,z3,z4,z6]),(0,[z288,z1,z2,z3,z4,z5,z6])],[(0,[z1,z289,z2,z3,z4,z5,z6]),(1,[z1,z2,z290,z4,z5,z6]),(0,[z1,z2,z291,z3,z4,z5,z6]),(0,[z1,z73,z2,z63,z3,z5,z6])],[(0,[z1,z2,z3,z4,z5,z292,z6]),(0,[z1,z2,z3,z4,z5,z293,z6]),(0,[z1,z294,z3,z4,z5,z6,z76]),(0,[z1,z2,z295,z3,z53,z4,z5]),(0,[z1,z296,z2,z3,z4,z5,z6]),(0,[z297,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z298,z3,z4,z5,z6])],[(0,[z1,z299,z2,z3,z4,z5,z6]),(0,[z97,z1,z2,z3,z4,z82,z6]),(0,[z1,z2,z3,z300,z4,z5,z6]),(0,[z1,z2,z3,z4,z301,z5,z6]),(0,[z1,z2,z302,z3,z4,z5,z6]),(0,[z1,z2,z49,z42,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z303]),(1,[z1,z2,z3,z4,z8,z6]),(0,[z1,z99,z31,z3,z4,z5,z6])],[(0,[z1,z2,z3,z304,z4,z5,z6]),(0,[z1,z2,z305,z3,z4,z5,z6])],[(0,[z306,z1,z2,z3,z4,z5,z6])],[(0,[z307,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z100,z4,z20,z6]),(0,[z1,z2,z3,z308,z4,z5,z6]),(1,[z1,z2,z3,z111,z6,z15]),(0,[z309,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z8,z6,z69]),(0,[z1,z2,z3,z4,z5,z310,z6]),(0,[z311,z1,z2,z3,z4,z5,z6])],[(1,[z17,z294,z3,z4,z5,z6]),(0,[z1,z2,z3,z312,z4,z5,z6]),(0,[z1,z2,z63,z3,z4,z8,z6]),(0,[z1,z146,z2,z3,z4,z20,z6]),(0,[z97,z1,z2,z3,z4,z5,z171]),(0,[z313,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z63,z3,z5,z9,z6]),(0,[z314,z1,z2,z3,z4,z5,z6]),(1,[z127,z1,z2,z315,z4,z5])],[(0,[z1,z2,z3,z4,z316,z5,z6]),(0,[z1,z2,z3,z4,z317,z5,z6]),(0,[z149,z1,z2,z3,z4,z20,z6]),(0,[z1,z2,z318,z3,z4,z5,z6]),(0,[z1,z2,z3,z319,z4,z5,z6])],[(0,[z1,z320,z2,z3,z4,z5,z6]),(0,[z1,z321,z2,z3,z4,z20,z6]),(0,[z1,z2,z3,z4,z322,z20,z6]),(0,[z1,z323,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z324]),(0,[z325,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z87,z3,z4,z5,z69]),(0,[z1,z2,z3,z326,z4,z5,z6])],[(0,[z97,z2,z3,z4,z5,z8,z6]),(0,[z1,z2,z327,z3,z4,z5,z6]),(0,[z46,z1,z2,z3,z4,z20,z6]),(1,[z1,z2,z79,z3,z4,z20]),(0,[z1,z2,z328,z3,z4,z5,z6])],[(0,[z1,z2,z329,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z330]),(0,[z1,z2,z3,z4,z5,z6,z331]),(0,[z1,z332,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z333,z4,z5,z6]),(0,[z1,z334,z2,z3,z4,z5,z6]),(0,[z149,z1,z2,z3,z4,z5,z28])],[(0,[z1,z2,z335,z3,z4,z5,z6]),(0,[z1,z2,z336,z3,z4,z5,z6]),(0,[z1,z73,z3,z100,z4,z5,z6]),(0,[z1,z2,z337,z3,z4,z5,z6]),(0,[z1,z338,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z339,z6])],[(0,[z1,z2,z3,z4,z121,z5,z6]),(0,[z1,z2,z340,z3,z4,z5,z6]),(0,[z341,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z68,z4,z5,z69])]],
   [[(1,[z1,z2,z3,z4,z5,z330]),(0,[z1,z2,z14,z3,z4,z20,z6]),(1,[z1,z2,z3,z4,z5,z331]),(1,[z46,z2,z3,z4,z5,z171]),(0,[z342,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z123,z3,z4,z5,z217]),(1,[z149,z1,z2,z47,z3,z4])],[(0,[z2,z187,z3,z85,z4,z5,z6]),(0,[z1,z2,z3,z85,z4,z20,z6]),(0,[z1,z2,z3,z4,z20,z20,z6]),(0,[z1,z2,z3,z4,z20,z56,z6]),(0,[z1,z2,z3,z343,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z344]),(0,[z1,z2,z3,z4,z5,z345,z6])],[(0,[z346,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z347,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z348]),(0,[z1,z48,z2,z3,z111,z4,z6]),(0,[z1,z2,z349,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z350])],[(0,[z1,z2,z3,z4,z351,z5,z6]),(0,[z352,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z315,z4,z8,z6]),(0,[z1,z2,z353,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z354,z6]),(0,[z1,z2,z355,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z356,z6]),(0,[z1,z2,z208,z3,z4,z8,z6]),(1,[z1,z2,z3,z4,z5,z344]),(0,[z1,z357,z2,z3,z4,z5,z6])],[(0,[z1,z358,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z8,z171,z6]),(0,[z1,z2,z3,z359,z4,z5,z6]),(0,[z1,z2,z41,z3,z4,z20,z6])],[(0,[z1,z294,z2,z3,z4,z8,z6]),(0,[z1,z2,z128,z3,z85,z4,z5]),(0,[z1,z2,z3,z4,z5,z6,z360]),(0,[z1,z99,z2,z3,z4,z20,z6]),(0,[z149,z361,z2,z3,z4,z5,z6])],[(0,[z1,z2,z362,z3,z4,z5,z6]),(0,[z1,z2,z3,z363,z4,z5,z6]),(0,[z1,z2,z3,z64,z4,z5,z6])]],
   [[(0,[z364,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z365,z5,z6])],[(1,[z58,z18,z3,z4,z5,z6]),(0,[z366,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z367,z4,z5,z6]),(0,[z368,z1,z2,z3,z4,z5,z6]),(0,[z1,z39,z3,z4,z5,z6,z76]),(0,[z1,z2,z369,z3,z4,z5,z6]),(0,[z1,z2,z3,z19,z4,z5,z6]),(0,[z1,z2,z370,z3,z4,z5,z6])],[],[(0,[z1,z371,z2,z3,z4,z5,z6]),(0,[z372,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z373,z3,z4,z5,z6])],[(0,[z81,z1,z2,z3,z54,z5,z6]),(0,[z107,z2,z3,z53,z4,z5,z6]),(0,[z1,z2,z374,z3,z4,z5,z6]),(1,[z1,z3,z4,z5,z130,z6])],[(0,[z1,z2,z3,z45,z4,z5,z6]),(0,[z1,z2,z3,z37,z4,z8,z6]),(0,[z97,z1,z2,z3,z4,z375,z6]),(0,[z1,z2,z3,z4,z5,z267,z6]),(0,[z1,z2,z3,z4,z158,z5,z6]),(0,[z1,z2,z3,z315,z4,z5,z159]),(0,[z1,z376,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z3,z4,z5,z6]),(0,[z1,z146,z2,z64,z4,z5,z6]),(0,[z1,z2,z377,z3,z4,z5,z6])],[(0,[z30,z1,z2,z37,z4,z5,z6]),(0,[z1,z99,z2,z3,z90,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z378]),(0,[z127,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z17,z1,z2,z3,z4,z8,z6]),(0,[z116,z1,z2,z3,z4,z165,z6]),(0,[z232,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z379,z4,z5,z6]),(0,[z1,z2,z3,z380,z4,z5,z6])],[(0,[z1,z2,z381,z3,z4,z5,z6]),(0,[z1,z382,z2,z3,z4,z5,z6])],[(0,[z383,z1,z2,z3,z4,z5,z6]),(0,[z1,z99,z2,z63,z3,z5,z6]),(0,[z1,z2,z384,z3,z4,z5,z6])],[(0,[z81,z1,z2,z3,z4,z218,z6]),(0,[z1,z2,z385,z3,z4,z5,z6]),(0,[z33,z1,z2,z3,z4,z8,z6]),(0,[z1,z48,z2,z3,z4,z20,z6]),(0,[z97,z1,z2,z3,z379,z5,z6]),(0,[z1,z2,z3,z386,z4,z5,z6]),(0,[z1,z2,z387,z3,z4,z5,z6])],[(0,[z388,z1,z2,z3,z4,z5,z6]),(1,[z1,z389,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z390,z6]),(0,[z1,z2,z3,z4,z5,z391,z6]),(0,[z392,z1,z2,z3,z4,z5,z6])],[(0,[z1,z3,z100,z4,z90,z5,z6])],[(0,[z1,z2,z18,z3,z4,z8,z6]),(0,[z1,z2,z3,z111,z4,z20,z6])],[(0,[z393,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z394,z4,z5,z6]),(0,[z395,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z396,z5,z6]),(0,[z1,z2,z87,z3,z4,z20,z6]),(0,[z1,z2,z3,z4,z5,z257,z6]),(0,[z1,z397,z2,z3,z4,z5,z6]),(0,[z1,z2,z42,z4,z5,z65,z6]),(0,[z1,z2,z398,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z53,z4,z5,z6]),(0,[z1,z2,z3,z4,z90,z20,z6]),(0,[z399,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z49,z3,z42,z4,z6]),(0,[z1,z2,z3,z400,z4,z5,z6]),(0,[z86,z1,z2,z3,z111,z5,z6]),(1,[z86,z1,z2,z87,z3,z5])],[(0,[z1,z2,z3,z401,z4,z5,z6]),(0,[z116,z1,z2,z85,z4,z5,z6]),(0,[z1,z2,z3,z4,z402,z5,z6]),(0,[z403,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z404]),(0,[z1,z2,z123,z3,z4,z8,z6]),(0,[z1,z405,z2,z3,z4,z5,z6]),(1,[z1,z61,z3,z4,z220,z6]),(0,[z1,z2,z3,z4,z5,z6,z217]),(0,[z1,z2,z123,z3,z5,z9,z6]),(0,[z1,z2,z3,z406,z4,z5,z6])],[(0,[z24,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z407,z5,z6])],[(0,[z1,z2,z3,z4,z5,z408,z6]),(0,[z409,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z410,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z411,z5,z6]),(0,[z1,z2,z3,z412,z4,z5,z6]),(0,[z1,z2,z49,z3,z4,z65,z6])],[(0,[z116,z2,z187,z3,z4,z5,z6]),(0,[z1,z39,z2,z3,z4,z8,z6]),(0,[z413,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z414]),(0,[z1,z2,z3,z4,z5,z6,z415])],[(0,[z58,z1,z294,z3,z4,z5,z6]),(0,[z127,z1,z2,z85,z4,z5,z6]),(0,[z1,z2,z3,z4,z20,z9,z6]),(0,[z1,z2,z3,z4,z5,z375,z6]),(0,[z416,z1,z2,z3,z4,z5,z6]),(0,[z417,z1,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z138,z5,z6])]],
   [[(1,[z232,z2,z3,z4,z20,z6]),(0,[z1,z2,z3,z4,z27,z20,z6]),(0,[z418,z1,z2,z3,z4,z5,z6]),(0,[z419,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z56,z6])],[(0,[z30,z1,z2,z3,z4,z20,z6]),(0,[z1,z2,z3,z4,z20,z6,z331]),(0,[z1,z2,z3,z4,z420,z5,z6]),(0,[z1,z2,z3,z4,z421,z5,z6])],[(0,[z1,z422,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z8,z77,z6]),(0,[z1,z2,z3,z423,z4,z5,z6]),(0,[z1,z2,z424,z3,z4,z5,z6])],[(0,[z58,z17,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z218,z6]),(0,[z1,z2,z425,z3,z4,z5,z6]),(0,[z1,z2,z3,z426,z4,z5,z6]),(0,[z427,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z87,z3,z315,z4,z5]),(0,[z1,z2,z3,z4,z27,z5,z28])],[(0,[z84,z1,z2,z187,z4,z5,z6]),(0,[z46,z1,z2,z87,z3,z4,z5]),(0,[z428,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z429,z3,z4,z5,z6])],[(0,[z430,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z20,z6]),(0,[z1,z2,z3,z4,z5,z431,z6]),(0,[z1,z432,z2,z3,z4,z5,z6]),(0,[z86,z1,z2,z87,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z28])],[(0,[z1,z2,z3,z433,z4,z5,z6]),(0,[z1,z2,z3,z434,z4,z5,z6]),(0,[z97,z232,z2,z3,z4,z5,z6]),(0,[z435,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z436,z4,z5,z6]),(1,[z1,z2,z3,z284,z5,z6])],[(0,[z1,z222,z2,z3,z4,z5,z6]),(0,[z33,z1,z3,z4,z5,z56,z6])]],
   [[(0,[z437,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z20,z6,z438]),(0,[z1,z439,z2,z3,z4,z5,z6]),(0,[z1,z61,z2,z14,z3,z4,z6]),(0,[z1,z2,z3,z4,z440,z5,z6]),(0,[z1,z2,z441,z3,z4,z5,z6])],[(0,[z1,z2,z3,z442,z4,z5,z6]),(0,[z1,z2,z3,z4,z8,z55,z6]),(0,[z46,z1,z2,z3,z4,z5,z171]),(0,[z1,z443,z2,z3,z4,z5,z6])],[(0,[z1,z2,z63,z3,z4,z20,z6]),(0,[z1,z2,z3,z4,z5,z6,z444]),(0,[z1,z2,z87,z3,z5,z6,z159])],[(0,[z1,z2,z3,z445,z4,z5,z6]),(0,[z446,z1,z2,z3,z4,z5,z6]),(0,[z97,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z447,z5,z6]),(0,[z448,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z449]),(0,[z450,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z451,z5,z6])],[(1,[z1,z2,z3,z4,z452,z6]),(0,[z116,z1,z2,z187,z4,z5,z6]),(0,[z1,z2,z3,z453,z4,z5,z6]),(0,[z1,z2,z49,z41,z4,z5,z6]),(0,[z149,z1,z2,z3,z111,z4,z6])],[(0,[z1,z2,z454,z3,z4,z5,z6])],[(0,[z455,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z456,z4,z5,z6]),(0,[z1,z2,z3,z4,z457,z5,z6]),(1,[z1,z2,z41,z4,z65,z6]),(0,[z1,z2,z68,z3,z4,z5,z6]),(0,[z1,z2,z3,z111,z5,z6,z15])],[(0,[z84,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z5,z6,z458]),(0,[z459,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z460])]],
   [[(1,[z1,z2,z128,z3,z4,z5]),(0,[z1,z2,z3,z461,z4,z5,z6])],[(0,[z1,z2,z187,z3,z4,z5,z6]),(0,[z97,z2,z3,z4,z5,z6,z122]),(1,[z361,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z359,z4,z8,z6]),(0,[z1,z2,z3,z42,z4,z5,z6]),(0,[z1,z2,z462,z3,z4,z5,z6])],[(0,[z58,z1,z18,z3,z4,z5,z6]),(0,[z1,z2,z463,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z464]),(1,[z1,z2,z3,z465,z4,z6]),(0,[z1,z2,z466,z3,z4,z5,z6]),(0,[z1,z2,z467,z3,z4,z5,z6])],[(0,[z468,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z64,z4,z8,z6]),(0,[z1,z2,z3,z315,z4,z20,z6]),(0,[z46,z1,z2,z3,z4,z255,z6]),(0,[z1,z2,z47,z3,z4,z6,z28])],[(0,[z1,z2,z3,z4,z5,z114,z6]),(0,[z1,z2,z3,z469,z4,z5,z6]),(0,[z1,z2,z3,z4,z8,z6,z15]),(0,[z46,z1,z2,z3,z4,z5,z122]),(0,[z1,z2,z3,z470,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z471]),(0,[z1,z2,z3,z4,z5,z6,z472])],[(0,[z30,z1,z2,z64,z4,z5,z6]),(0,[z1,z2,z3,z4,z473,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z474]),(0,[z1,z475,z2,z3,z4,z5,z6])],[(0,[z1,z294,z2,z3,z4,z20,z6]),(0,[z116,z1,z2,z3,z4,z8,z6]),(0,[z97,z1,z2,z87,z3,z4,z5]),(0,[z1,z61,z2,z3,z4,z5,z6]),(0,[z1,z2,z41,z3,z111,z4,z6])]],
   [[(1,[z1,z2,z3,z4,z351,z6]),(0,[z1,z476,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z8,z65,z6]),(0,[z1,z2,z3,z4,z5,z477,z6]),(0,[z1,z2,z3,z478,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z479]),(0,[z1,z480,z2,z3,z4,z5,z6]),(0,[z481,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z482,z3,z4,z5,z6]),(0,[z30,z1,z3,z100,z4,z5,z6])],[(0,[z1,z2,z147,z3,z4,z5,z6]),(0,[z1,z2,z483,z3,z4,z5,z6])],[(0,[z127,z1,z2,z3,z4,z8,z6]),(0,[z1,z73,z2,z123,z3,z5,z6]),(0,[z1,z484,z2,z3,z4,z5,z6])],[(0,[z232,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z485,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z9,z6])],[(1,[z1,z2,z3,z4,z67,z6]),(0,[z486,z1,z2,z3,z4,z5,z6]),(1,[z1,z487,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z8,z488,z6]),(0,[z1,z2,z3,z37,z4,z20,z6]),(0,[z1,z489,z2,z3,z4,z5,z6]),(0,[z490,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z491,z3,z4,z5,z6]),(0,[z1,z492,z2,z3,z4,z5,z6]),(0,[z107,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z49,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z493,z5,z6]),(0,[z1,z2,z494,z3,z4,z5,z6])]],
   [[(0,[z97,z1,z222,z3,z4,z5,z6]),(0,[z1,z99,z3,z4,z90,z5,z6]),(0,[z1,z2,z3,z4,z220,z5,z6]),(0,[z1,z2,z495,z3,z4,z5,z6])],[(0,[z17,z1,z2,z3,z4,z20,z6]),(0,[z81,z2,z3,z4,z54,z5,z6]),(0,[z496,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z497])],[(0,[z498,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z499,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z500,z6])],[(0,[z1,z2,z3,z501,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z502,z6])],[(0,[z84,z2,z3,z85,z4,z5,z6]),(0,[z86,z1,z2,z3,z54,z5,z6]),(0,[z1,z2,z503,z3,z4,z5,z6]),(0,[z1,z2,z198,z3,z4,z8,z6]),(0,[z33,z1,z2,z3,z4,z20,z6]),(0,[z504,z1,z2,z3,z4,z5,z6]),(0,[z1,z73,z2,z3,z4,z5,z6]),(1,[z1,z99,z3,z90,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z505]),(0,[z1,z2,z3,z4,z5,z6,z506]),(0,[z164,z149,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z53,z4,z8,z6]),(1,[z2,z3,z4,z8,z171,z6]),(0,[z1,z2,z3,z4,z199,z8,z6]),(0,[z1,z2,z3,z507,z4,z5,z6]),(1,[z1,z2,z508,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z509,z6]),(0,[z97,z1,z2,z510,z4,z5,z6]),(0,[z2,z3,z4,z5,z171,z6,z122]),(0,[z1,z2,z3,z4,z5,z6,z511]),(0,[z512,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z26,z4,z5,z6])],[(0,[z1,z2,z18,z3,z4,z20,z6]),(0,[z1,z2,z3,z4,z5,z6,z438])]],
   [[(0,[z1,z2,z3,z4,z5,z6,z513]),(0,[z514,z1,z2,z3,z4,z5,z6]),(0,[z97,z1,z2,z3,z4,z5,z122]),(0,[z1,z2,z3,z515,z4,z5,z6]),(0,[z1,z2,z14,z3,z4,z6,z28]),(0,[z1,z2,z3,z4,z5,z6,z516])],[(0,[z1,z88,z2,z3,z4,z5,z6]),(0,[z1,z517,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z20,z6,z28]),(0,[z1,z2,z205,z3,z4,z5,z6]),(0,[z1,z2,z518,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z69])],[(0,[z1,z2,z3,z4,z519,z5,z6]),(0,[z1,z2,z520,z3,z4,z5,z6]),(0,[z1,z2,z3,z521,z4,z5,z6]),(0,[z1,z2,z3,z4,z522,z5,z6])],[(0,[z1,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z123,z3,z4,z20,z6]),(0,[z1,z2,z523,z3,z4,z5,z6]),(0,[z1,z524,z2,z3,z4,z5,z6]),(0,[z1,z2,z47,z3,z4,z5,z6])],[(0,[z1,z2,z3,z525,z4,z5,z6]),(0,[z24,z1,z2,z3,z4,z20,z6]),(0,[z1,z2,z315,z4,z5,z6,z69]),(0,[z1,z526,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z8,z6,z122]),(0,[z1,z2,z3,z4,z5,z527,z6]),(0,[z1,z2,z3,z528,z4,z5,z6])],[(0,[z1,z39,z2,z3,z4,z20,z6]),(0,[z1,z529,z2,z3,z4,z5,z6]),(0,[z530,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z531,z5,z6]),(0,[z1,z2,z532,z3,z4,z5,z6]),(0,[z1,z36,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z533,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z247,z6])],[(0,[z1,z487,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z534,z6]),(0,[z1,z2,z3,z53,z4,z5,z330]),(0,[z1,z2,z3,z4,z535,z5,z6]),(0,[z1,z536,z2,z3,z4,z5,z6]),(0,[z127,z1,z2,z315,z4,z5,z6])],[(0,[z84,z116,z2,z3,z4,z5,z6]),(0,[z1,z2,z295,z3,z4,z5,z6]),(0,[z232,z2,z3,z4,z20,z5,z6]),(0,[z1,z2,z537,z3,z4,z5,z6]),(0,[z538,z1,z2,z3,z4,z5,z6])],[(0,[z1,z539,z2,z3,z4,z5,z6]),(0,[z1,z2,z14,z198,z3,z4,z6])],[(0,[z1,z2,z3,z4,z540,z5,z6]),(0,[z1,z2,z3,z541,z4,z5,z6]),(0,[z1,z2,z542,z3,z4,z5,z6])],[(0,[z97,z33,z1,z2,z3,z4,z5]),(1,[z1,z2,z3,z4,z267,z6])],[(0,[z58,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z100,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z543,z6])],[(0,[z149,z1,z2,z3,z4,z27,z6])]],
   [[(0,[z1,z2,z3,z544,z4,z5,z6]),(0,[z81,z1,z2,z3,z4,z20,z6]),(0,[z1,z2,z31,z3,z4,z8,z6]),(0,[z1,z146,z2,z3,z4,z5,z6]),(0,[z1,z545,z2,z3,z4,z5,z6]),(1,[z1,z223,z3,z4,z5,z6])],[(0,[z107,z81,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z546,z4,z5,z6])],[(0,[z1,z2,z152,z3,z4,z5,z6]),(0,[z60,z1,z2,z3,z4,z20,z6]),(0,[z33,z46,z1,z2,z3,z4,z5]),(0,[z30,z1,z146,z3,z4,z5,z6]),(0,[z1,z2,z87,z3,z26,z4,z6])],[(0,[z17,z294,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z8,z8,z6]),(0,[z1,z2,z68,z3,z4,z8,z6]),(0,[z46,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z547,z6])],[(0,[z58,z1,z2,z3,z4,z67,z6]),(1,[z1,z221,z2,z3,z4,z5]),(1,[z1,z2,z3,z4,z237,z6]),(0,[z1,z2,z3,z4,z5,z6,z548]),(1,[z1,z2,z3,z4,z255,z6]),(0,[z1,z2,z3,z4,z5,z549,z6]),(0,[z550,z1,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z20,z331]),(0,[z551,z1,z2,z3,z4,z5,z6]),(0,[z1,z99,z73,z3,z4,z5,z6]),(0,[z1,z2,z552,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z553,z6]),(0,[z1,z2,z3,z111,z4,z6,z28]),(0,[z1,z2,z3,z4,z5,z6,z554])],[(0,[z86,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z42,z4,z8,z6]),(0,[z1,z2,z3,z4,z5,z555,z6]),(0,[z1,z2,z49,z3,z111,z4,z6]),(0,[z1,z2,z14,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z556,z6]),(0,[z84,z1,z2,z3,z4,z20,z6]),(0,[z1,z2,z3,z85,z4,z5,z6]),(0,[z557,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z20,z5,z6]),(0,[z1,z181,z2,z3,z4,z5,z6]),(0,[z1,z2,z347,z3,z4,z20,z6]),(0,[z558,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z559,z5,z6]),(0,[z1,z560,z2,z3,z4,z5,z6])],[(0,[z1,z2,z561,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z562,z6]),(0,[z1,z2,z3,z4,z20,z6,z159]),(0,[z1,z3,z4,z220,z5,z55,z6]),(0,[z1,z2,z3,z563,z4,z5,z6])],[(1,[z81,z2,z3,z54,z5,z6]),(0,[z1,z299,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z20,z564,z6]),(0,[z1,z2,z565,z3,z4,z5,z6]),(0,[z1,z48,z2,z3,z4,z220,z6]),(0,[z1,z48,z2,z14,z3,z4,z6]),(0,[z1,z2,z3,z566,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z567])],[(0,[z1,z2,z3,z4,z8,z6,z76]),(0,[z1,z2,z3,z568,z4,z5,z6]),(0,[z1,z2,z198,z3,z111,z4,z6])],[(0,[z1,z2,z3,z4,z54,z5,z6]),(0,[z107,z1,z2,z3,z4,z237,z6]),(0,[z1,z2,z3,z569,z4,z5,z6]),(0,[z1,z2,z3,z64,z4,z20,z6]),(0,[z1,z99,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z570,z6])],[(0,[z1,z2,z3,z4,z5,z6,z189]),(0,[z571,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z375,z6]),(0,[z572,z1,z2,z3,z4,z5,z6])],[(0,[z84,z1,z2,z3,z4,z452,z6]),(0,[z107,z1,z2,z3,z54,z5,z6]),(0,[z1,z2,z3,z4,z20,z6,z15]),(0,[z1,z2,z87,z3,z4,z5,z76]),(0,[z1,z2,z3,z4,z5,z573,z6])]],
   [[(0,[z574,z1,z2,z3,z4,z5,z6]),(0,[z116,z1,z2,z3,z4,z20,z6]),(0,[z1,z2,z3,z4,z138,z5,z6]),(1,[z97,z2,z3,z4,z5,z122]),(0,[z1,z2,z3,z4,z5,z575,z6]),(0,[z1,z2,z508,z3,z4,z5,z6]),(0,[z1,z2,z3,z465,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z576,z6])],[(0,[z577,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z68,z4,z5,z6,z69]),(0,[z86,z1,z2,z3,z4,z5,z159]),(0,[z1,z2,z3,z578,z4,z5,z6]),(0,[z1,z2,z579,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z20,z65,z6]),(0,[z97,z1,z2,z68,z3,z4,z5]),(0,[z1,z580,z2,z3,z4,z5,z6]),(0,[z164,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z581,z6]),(0,[z1,z61,z2,z3,z4,z220,z6]),(0,[z1,z2,z40,z3,z4,z9,z6]),(0,[z1,z582,z2,z3,z4,z5,z6])],[(0,[z583,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z187,z4,z5,z6,z69]),(0,[z1,z2,z3,z4,z584,z5,z6]),(0,[z1,z2,z327,z3,z4,z8,z6]),(1,[z1,z2,z3,z379,z5,z6]),(0,[z1,z585,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z586,z5,z6])],[(0,[z1,z2,z587,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z220,z8,z6]),(0,[z1,z2,z3,z4,z20,z6,z69]),(0,[z127,z1,z2,z3,z4,z20,z6]),(0,[z46,z2,z3,z4,z5,z171,z6])],[(0,[z1,z2,z588,z3,z4,z5,z6]),(0,[z232,z1,z2,z3,z4,z20,z6]),(0,[z1,z2,z3,z589,z4,z5,z6]),(1,[z1,z2,z520,z3,z4,z6])],[(0,[z1,z2,z590,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z591]),(0,[z1,z2,z3,z4,z115,z5,z6]),(0,[z1,z31,z3,z37,z4,z5,z6]),(1,[z1,z48,z3,z4,z55,z6]),(0,[z1,z2,z592,z3,z4,z5,z6]),(0,[z593,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z284,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z452,z5,z6]),(0,[z107,z1,z2,z3,z4,z20,z6]),(0,[z1,z2,z49,z3,z4,z20,z6]),(0,[z1,z2,z3,z594,z4,z5,z6])],[],[(0,[z595,z1,z2,z3,z4,z5,z6]),(0,[z1,z48,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z596,z4,z5,z6]),(0,[z1,z2,z3,z597,z4,z5,z6])],[(0,[z1,z598,z2,z3,z4,z5,z6]),(0,[z1,z2,z599,z3,z4,z5,z6]),(0,[z1,z61,z2,z49,z3,z4,z6])],[(0,[z127,z1,z2,z187,z4,z5,z6]),(0,[z1,z2,z3,z89,z4,z5,z6]),(0,[z600,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z394,z4,z20,z6]),(0,[z1,z2,z198,z3,z4,z20,z6]),(0,[z1,z61,z2,z3,z4,z55,z6]),(0,[z1,z2,z3,z4,z601,z5,z6]),(0,[z1,z2,z3,z111,z4,z5,z6]),(0,[z1,z2,z47,z3,z4,z27,z5])],[(0,[z1,z2,z3,z54,z5,z6,z159]),(0,[z1,z2,z3,z4,z5,z6,z602]),(0,[z1,z603,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z604,z5,z6]),(0,[z1,z2,z87,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z90,z5,z6]),(0,[z1,z2,z605,z3,z4,z5,z6])]],
   [[(0,[z2,z3,z4,z20,z5,z8,z6]),(0,[z1,z2,z3,z606,z4,z5,z6]),(0,[z1,z2,z607,z3,z4,z5,z6]),(0,[z1,z2,z608,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z609,z5,z6]),(1,[z2,z3,z4,z20,z8,z6]),(0,[z1,z2,z3,z19,z4,z8,z6]),(1,[z1,z2,z123,z5,z9,z6]),(0,[z127,z1,z2,z3,z315,z4,z5]),(0,[z86,z1,z2,z3,z19,z5,z6])],[(0,[z1,z2,z214,z3,z4,z5,z6]),(0,[z1,z2,z3,z610,z4,z5,z6]),(0,[z611,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z19,z5,z6,z159])],[(0,[z612,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z290,z4,z5,z6]),(0,[z1,z2,z613,z3,z4,z5,z6])],[(1,[z116,z2,z187,z4,z5,z6]),(0,[z1,z1,z2,z3,z4,z20,z6]),(0,[z1,z2,z3,z4,z5,z614,z6]),(0,[z86,z1,z2,z198,z3,z5,z6]),(0,[z1,z2,z87,z3,z4,z500,z6])],[(0,[z1,z18,z3,z4,z5,z6,z76]),(0,[z615,z1,z2,z3,z4,z5,z6]),(0,[z1,z223,z3,z4,z5,z9,z6]),(0,[z616,z1,z2,z3,z4,z5,z6])],[(0,[z97,z1,z2,z47,z3,z4,z5]),(0,[z1,z2,z617,z3,z4,z5,z6])],[(0,[z1,z389,z2,z18,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z5,z6]),(0,[z97,z127,z1,z2,z3,z4,z5]),(0,[z1,z2,z618,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z573]),(0,[z1,z2,z3,z4,z5,z6,z619])]],
   [[(0,[z1,z2,z3,z620,z4,z5,z6]),(0,[z30,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z520,z3,z4,z90,z6]),(0,[z1,z621,z2,z3,z4,z5,z6]),(0,[z149,z1,z2,z47,z3,z4,z6])],[(0,[z1,z2,z85,z4,z5,z6,z69]),(0,[z81,z1,z2,z3,z53,z5,z6]),(0,[z46,z1,z39,z2,z3,z4,z5]),(0,[z1,z2,z3,z622,z4,z5,z6]),(0,[z1,z2,z623,z3,z4,z5,z6]),(0,[z624,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z159]),(0,[z1,z2,z47,z3,z92,z5,z6])],[(0,[z1,z2,z3,z4,z5,z564,z6]),(0,[z1,z2,z3,z4,z5,z625,z6]),(0,[z1,z2,z63,z64,z4,z5,z6]),(0,[z1,z626,z2,z3,z4,z5,z6])],[(0,[z627,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z385,z3,z4,z8,z6]),(0,[z1,z99,z2,z3,z4,z5,z257]),(0,[z1,z2,z3,z628,z4,z5,z6]),(0,[z1,z2,z3,z19,z4,z5,z159])],[(0,[z1,z629,z2,z3,z4,z5,z6]),(0,[z1,z146,z2,z31,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z165,z6]),(0,[z1,z2,z3,z630,z4,z5,z6])],[(0,[z1,z2,z3,z4,z8,z6,z207]),(0,[z1,z631,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z56,z6,z76]),(0,[z1,z2,z632,z3,z4,z5,z6]),(0,[z1,z2,z633,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z15])],[(0,[z58,z1,z2,z3,z4,z20,z6]),(0,[z634,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z635,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z172,z3,z37,z4,z6]),(0,[z1,z2,z636,z3,z4,z5,z6]),(0,[z637,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z14,z3,z111,z5,z6]),(0,[z1,z2,z198,z3,z5,z6,z159]),(0,[z1,z361,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z53,z5,z6,z159]),(0,[z1,z2,z31,z3,z4,z20,z6]),(0,[z446,z1,z2,z3,z4,z20,z6]),(0,[z1,z2,z3,z4,z638,z5,z6]),(0,[z1,z2,z3,z4,z5,z65,z6]),(0,[z1,z2,z3,z639,z4,z5,z6])],[(0,[z1,z389,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z640,z4,z5,z6]),(0,[z232,z60,z2,z3,z4,z5,z6]),(0,[z60,z2,z3,z4,z5,z8,z6]),(0,[z1,z2,z79,z3,z4,z20,z6]),(1,[z1,z146,z31,z4,z5,z6]),(1,[z1,z2,z3,z4,z500,z6]),(0,[z1,z2,z3,z641,z4,z5,z6])],[(0,[z1,z2,z3,z642,z4,z5,z6]),(0,[z1,z643,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z644,z6]),(0,[z1,z2,z410,z3,z4,z8,z6]),(0,[z1,z2,z276,z3,z4,z20,z6]),(0,[z97,z1,z2,z3,z4,z5,z28])],[(0,[z1,z2,z3,z645,z4,z5,z6]),(0,[z17,z1,z2,z3,z4,z71,z6]),(0,[z1,z2,z3,z85,z4,z8,z6]),(0,[z1,z2,z3,z646,z4,z5,z6]),(0,[z1,z2,z198,z3,z5,z6,z15]),(0,[z149,z1,z2,z14,z3,z4,z6])],[(0,[z1,z2,z647,z3,z4,z5,z6]),(0,[z1,z2,z508,z4,z90,z5,z6]),(0,[z648,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z649,z6])],[(0,[z1,z2,z650,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z488,z6]),(1,[z1,z2,z3,z4,z82,z6]),(0,[z1,z2,z3,z4,z5,z651,z6]),(0,[z652,z1,z2,z3,z4,z5,z6])]],
   [[(1,[z1,z2,z295,z3,z4,z5]),(0,[z86,z1,z2,z3,z4,z20,z6]),(0,[z1,z2,z3,z42,z4,z20,z6]),(0,[z1,z2,z3,z653,z4,z5,z6])],[(0,[z1,z2,z510,z3,z4,z5,z6]),(0,[z1,z654,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z54,z8,z6]),(0,[z1,z655,z2,z3,z4,z5,z6])],[(0,[z1,z2,z656,z3,z4,z5,z6]),(0,[z1,z48,z3,z4,z5,z55,z6]),(0,[z1,z2,z3,z4,z5,z657,z6]),(0,[z1,z2,z3,z315,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z658,z6])],[(0,[z1,z487,z2,z3,z85,z4,z5]),(0,[z659,z1,z2,z3,z4,z5,z6]),(0,[z97,z1,z39,z2,z3,z4,z5]),(0,[z1,z2,z172,z3,z4,z5,z6]),(0,[z33,z1,z2,z3,z4,z5,z76]),(0,[z1,z2,z3,z660,z4,z5,z6]),(0,[z1,z2,z661,z3,z4,z5,z6]),(0,[z127,z1,z2,z3,z4,z5,z69]),(0,[z1,z662,z2,z3,z4,z5,z6])],[(0,[z17,z1,z294,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z663]),(0,[z97,z1,z129,z3,z4,z5,z6])],[(0,[z1,z294,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z434,z4,z8,z6]),(0,[z30,z1,z99,z3,z4,z5,z6])],[(0,[z664,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z33,z1,z294,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z247,z6]),(0,[z97,z1,z2,z290,z4,z5,z6]),(0,[z1,z2,z68,z3,z315,z4,z5])],[(0,[z17,z1,z2,z3,z4,z114,z6]),(0,[z1,z2,z3,z4,z71,z5,z6]),(0,[z665,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z666,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z20,z5,z331]),(0,[z1,z2,z3,z667,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z668,z6])],[(0,[z58,z1,z2,z3,z4,z351,z6]),(0,[z46,z1,z2,z68,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z6,z669]),(0,[z1,z146,z2,z123,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z670,z6]),(0,[z1,z2,z3,z4,z5,z56,z159]),(0,[z1,z2,z3,z4,z5,z671,z6])],[(0,[z97,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z317,z20,z6]),(0,[z1,z2,z3,z4,z672,z5,z6]),(0,[z1,z73,z2,z3,z100,z5,z6]),(0,[z1,z2,z3,z4,z673,z5,z6]),(0,[z674,z1,z2,z3,z4,z5,z6]),(0,[z675,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z8,z171,z6]),(0,[z1,z2,z3,z4,z5,z69,z159]),(0,[z149,z1,z2,z3,z4,z5,z6]),(0,[z676,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z322,z5,z6]),(0,[z1,z321,z2,z3,z4,z5,z6]),(0,[z1,z2,z491,z3,z4,z20,z6]),(0,[z1,z2,z3,z4,z5,z677,z6]),(0,[z1,z2,z3,z37,z4,z5,z6]),(0,[z678,z1,z2,z3,z4,z5,z6])],[(0,[z679,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z680,z6]),(0,[z1,z2,z3,z681,z4,z5,z6]),(0,[z1,z2,z3,z4,z20,z55,z6]),(0,[z1,z2,z3,z4,z220,z20,z6]),(1,[z1,z2,z205,z3,z5,z6]),(0,[z1,z2,z3,z465,z4,z90,z6]),(0,[z682,z1,z2,z3,z4,z5,z6]),(0,[z1,z39,z2,z3,z4,z5,z76]),(0,[z1,z2,z3,z4,z5,z130,z6])],[(0,[z1,z2,z3,z683,z4,z5,z6]),(1,[z1,z2,z510,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z684,z6]),(0,[z1,z2,z3,z685,z4,z5,z6]),(0,[z1,z2,z3,z4,z686,z5,z6])]],
   [[(0,[z17,z1,z2,z3,z4,z5,z6]),(0,[z1,z99,z2,z123,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z687,z6])],[(0,[z1,z2,z187,z3,z4,z8,z6]),(0,[z1,z61,z48,z3,z4,z5,z6]),(0,[z688,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z689,z6]),(0,[z33,z1,z39,z3,z4,z5,z6]),(0,[z1,z2,z3,z690,z4,z5,z6])],[(0,[z1,z691,z2,z3,z4,z5,z6]),(0,[z1,z99,z2,z3,z4,z5,z344]),(0,[z1,z2,z3,z4,z5,z692,z6]),(0,[z1,z2,z3,z4,z5,z6,z693]),(0,[z1,z2,z3,z694,z4,z5,z6])],[(0,[z1,z2,z695,z3,z4,z5,z6]),(0,[z33,z1,z2,z3,z4,z5,z6]),(0,[z1,z696,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z697,z6]),(1,[z1,z2,z14,z198,z3,z6])],[(0,[z1,z2,z3,z4,z90,z8,z6]),(0,[z1,z146,z31,z3,z4,z5,z6])],[(0,[z1,z698,z2,z3,z4,z5,z6]),(0,[z1,z2,z123,z3,z4,z5,z573]),(0,[z699,z1,z2,z3,z4,z5,z6])],[(0,[z294,z2,z18,z3,z4,z5,z6]),(0,[z1,z2,z18,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z260,z6]),(0,[z1,z2,z700,z3,z4,z5,z6]),(0,[z701,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z702,z3,z4,z5,z6]),(0,[z1,z2,z703,z3,z4,z5,z6]),(0,[z1,z61,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z5,z704,z6]),(0,[z1,z2,z41,z3,z4,z5,z6]),(0,[z705,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z706,z3,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z294,z707,z3,z4,z5,z6]),(0,[z1,z222,z3,z379,z5,z6]),(0,[z1,z2,z124,z147,z3,z6])],[(0,[z116,z2,z187,z4,z165,z6]),(0,[z1,z2,z3,z708,z4,z5]),(0,[z1,z2,z3,z4,z35,z28]),(0,[z1,z2,z147,z3,z20,z6]),(0,[z1,z2,z3,z4,z5,z709])],[(0,[z1,z2,z3,z4,z710,z6]),(0,[z1,z2,z3,z4,z711,z6]),(0,[z1,z2,z3,z4,z5,z712]),(0,[z1,z2,z3,z4,z713,z6]),(0,[z1,z2,z3,z4,z714,z6])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z8,z715]),(0,[z1,z2,z3,z4,z716,z6]),(0,[z33,z1,z3,z4,z5,z709])],[(1,[z2,z79,z3,z4,z8]),(0,[z585,z2,z3,z4,z8,z6]),(0,[z1,z223,z3,z4,z8,z6]),(0,[z1,z2,z3,z717,z8,z6]),(0,[z149,z1,z2,z79,z3,z4]),(0,[z1,z2,z3,z718,z5,z6]),(0,[z1,z2,z719,z4,z5,z6])],[(0,[z1,z2,z720,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z721])],[(0,[z1,z2,z3,z4,z722,z6])],[(0,[z1,z723,z3,z4,z5,z6]),(0,[z2,z592,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z20,z724]),(0,[z1,z2,z64,z407,z5,z6]),(0,[z1,z2,z725,z3,z4,z6])]],
   [[(0,[z1,z2,z3,z726,z5,z6]),(0,[z164,z2,z3,z4,z5,z6]),(0,[z97,z2,z3,z4,z8,z171]),(0,[z1,z2,z3,z4,z727,z6]),(0,[z1,z2,z4,z728,z65,z6])],[(0,[z1,z2,z729,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z730]),(0,[z446,z1,z2,z79,z3,z4]),(0,[z1,z146,z31,z4,z5,z6]),(1,[z1,z2,z3,z731,z6]),(0,[z1,z2,z3,z4,z500,z6])],[(0,[z1,z2,z3,z4,z732,z6]),(0,[z1,z2,z733,z3,z4,z6]),(0,[z1,z734,z3,z4,z5,z6]),(0,[z116,z2,z735,z4,z5,z6]),(0,[z1,z2,z89,z4,z20,z6])],[(0,[z1,z321,z3,z4,z21,z6]),(1,[z30,z1,z205,z5,z6]),(0,[z1,z2,z123,z5,z9,z217])],[(0,[z1,z129,z3,z4,z375,z6]),(0,[z97,z1,z2,z3,z4,z500]),(0,[z1,z2,z3,z4,z736,z6]),(0,[z1,z2,z3,z4,z737,z6]),(0,[z1,z738,z3,z4,z5,z6]),(0,[z1,z2,z41,z4,z728,z6])],[(0,[z1,z2,z3,z4,z739,z6]),(0,[z46,z2,z3,z4,z267,z171])],[(0,[z1,z2,z3,z4,z740,z6]),(0,[z1,z2,z3,z4,z121,z6]),(0,[z1,z2,z3,z4,z5,z741]),(0,[z603,z2,z3,z4,z8,z6]),(0,[z1,z742,z3,z4,z5,z6]),(0,[z361,z2,z3,z4,z20,z6]),(0,[z97,z129,z3,z4,z5,z122])],[(0,[z81,z2,z3,z54,z8,z6]),(0,[z107,z2,z3,z53,z247,z6]),(0,[z1,z2,z743,z3,z4,z6]),(0,[z1,z2,z290,z4,z375,z6]),(0,[z1,z2,z3,z4,z744,z6])]],
   [[],[(0,[z1,z2,z290,z4,z20,z6]),(0,[z97,z2,z290,z4,z5,z122]),(0,[z1,z2,z49,z4,z728,z6])],[(0,[z1,z2,z3,z745,z5,z6]),(0,[z97,z2,z510,z4,z8,z6]),(0,[z1,z2,z3,z708,z4,z20]),(0,[z1,z129,z3,z379,z5,z6]),(0,[z33,z1,z3,z4,z5,z56])],[(0,[z1,z2,z3,z4,z746,z6]),(0,[z1,z2,z747,z3,z5,z6]),(0,[z2,z3,z4,z35,z8,z171]),(0,[z1,z2,z3,z4,z20,z748]),(0,[z1,z2,z3,z749,z4,z20]),(0,[z1,z2,z3,z750,z4,z6]),(0,[z1,z2,z3,z4,z751,z6])],[(0,[z1,z2,z3,z4,z752,z6]),(0,[z97,z2,z3,z4,z8,z122]),(0,[z1,z88,z3,z4,z199,z6]),(0,[z1,z2,z3,z753,z5,z6])],[(0,[z1,z2,z754,z3,z4,z6]),(0,[z1,z755,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z255,z331]),(0,[z1,z2,z3,z756,z4,z6]),(0,[z1,z2,z3,z4,z757,z6]),(0,[z1,z2,z3,z4,z758,z6]),(0,[z149,z1,z2,z3,z694,z4])],[(0,[z1,z2,z3,z759,z5,z6])],[(0,[z1,z2,z760,z4,z5,z6]),(0,[z1,z2,z3,z4,z247,z6]),(0,[z1,z508,z100,z4,z5,z6]),(0,[z1,z2,z761,z4,z5,z69])]],
   [[(0,[z1,z222,z3,z4,z5,z6]),(0,[z127,z1,z2,z761,z4,z5])],[(0,[z1,z2,z3,z762,z5,z6]),(0,[z1,z2,z508,z520,z4,z6]),(0,[z1,z2,z3,z763,z5,z6]),(0,[z1,z3,z4,z220,z764,z6]),(0,[z1,z3,z4,z158,z130,z6]),(0,[z1,z2,z3,z4,z765,z6])],[],[(0,[z1,z2,z3,z4,z766,z5])],[(0,[z1,z2,z767,z4,z5,z6]),(0,[z1,z2,z3,z4,z768,z6]),(0,[z1,z2,z68,z290,z4,z5]),(1,[z1,z769,z4,z5,z6]),(0,[z1,z770,z3,z4,z5,z6])],[(0,[z1,z2,z205,z3,z5,z6])],[(0,[z1,z2,z510,z4,z5,z6]),(0,[z1,z2,z771,z4,z8,z6]),(0,[z309,z2,z3,z4,z8,z6]),(0,[z512,z2,z3,z4,z20,z6]),(0,[z1,z2,z3,z4,z772,z6]),(0,[z1,z2,z3,z4,z773,z6])],[(0,[z1,z2,z3,z4,z774,z6]),(0,[z1,z2,z3,z4,z5,z775]),(0,[z1,z2,z3,z4,z776,z6]),(0,[z1,z2,z777,z4,z5,z6])]],
   [[(0,[z97,z2,z3,z4,z778,z6]),(0,[z143,z2,z3,z4,z8,z6]),(0,[z46,z2,z3,z4,z20,z171]),(0,[z1,z2,z214,z394,z4,z6]),(0,[z1,z2,z3,z779,z4,z6])],[(0,[z1,z99,z3,z90,z20,z6]),(0,[z780,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z257]),(0,[z1,z3,z4,z5,z709,z76]),(0,[z1,z123,z5,z130,z9,z6])],[(0,[z1,z2,z3,z4,z781,z6]),(0,[z278,z18,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z782,z6]),(0,[z97,z2,z3,z379,z8,z6]),(0,[z232,z2,z79,z3,z4,z5]),(0,[z1,z2,z508,z4,z20,z6]),(0,[z1,z2,z63,z64,z5,z6]),(0,[z1,z2,z3,z92,z6,z28])],[(0,[z1,z2,z3,z4,z5,z783]),(0,[z1,z2,z3,z4,z784,z6]),(0,[z1,z2,z785,z3,z4,z6]),(0,[z1,z786,z2,z3,z4,z5])],[(0,[z1,z2,z3,z787,z5,z6])],[(0,[z1,z3,z4,z5,z788,z6]),(0,[z550,z2,z3,z4,z8,z6]),(0,[z699,z2,z3,z4,z20,z6]),(0,[z97,z2,z3,z150,z4,z5]),(0,[z1,z2,z3,z4,z420,z28])],[(0,[z1,z2,z789,z4,z5,z6]),(0,[z1,z36,z3,z4,z220,z6]),(0,[z1,z2,z3,z4,z5,z790]),(0,[z1,z2,z791,z3,z5,z6]),(0,[z1,z2,z3,z792,z5,z6])],[(0,[z1,z2,z79,z3,z4,z5]),(0,[z705,z2,z3,z4,z8,z6]),(0,[z1,z2,z520,z89,z4,z6]),(0,[z1,z2,z793,z4,z5,z6])]],
   [[(0,[z116,z2,z187,z4,z8,z6]),(1,[z2,z3,z4,z5,z794]),(0,[z1,z2,z3,z4,z795,z6])],[(0,[z654,z2,z3,z4,z8,z6]),(0,[z1,z181,z3,z4,z55,z6]),(0,[z1,z3,z4,z20,z130,z6])],[(0,[z1,z2,z3,z4,z260,z6]),(0,[z593,z2,z85,z4,z5,z6])],[(0,[z1,z2,z3,z4,z796,z6]),(0,[z1,z2,z3,z4,z8,z573]),(0,[z311,z2,z3,z4,z8,z6]),(0,[z1,z2,z49,z412,z4,z6])],[(0,[z1,z2,z797,z3,z5,z6]),(0,[z1,z2,z295,z3,z4,z8]),(0,[z1,z2,z3,z359,z6,z15]),(0,[z1,z2,z3,z4,z82,z28]),(0,[z30,z1,z37,z4,z5,z6]),(0,[z1,z2,z40,z3,z4,z6]),(0,[z1,z2,z3,z4,z798,z6]),(0,[z1,z2,z3,z799,z4,z6])],[(0,[z1,z2,z3,z4,z5,z800]),(0,[z1,z2,z14,z3,z4,z331]),(0,[z1,z2,z801,z4,z5,z6]),(0,[z1,z2,z802,z3,z4,z6]),(0,[z1,z2,z3,z4,z803,z6])],[(0,[z17,z294,z3,z4,z114,z6]),(0,[z2,z3,z4,z8,z671,z6]),(0,[z1,z2,z47,z3,z4,z255])],[(0,[z1,z2,z804,z4,z5,z6]),(0,[z1,z2,z3,z805,z5,z6]),(0,[z1,z2,z806,z3,z4,z6])]],
   [[(0,[z1,z2,z508,z465,z4,z6]),(0,[z807,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z709,z6])],[(0,[z1,z2,z3,z4,z808,z6]),(0,[z1,z2,z3,z4,z809,z6]),(0,[z1,z2,z3,z4,z5,z810]),(0,[z1,z2,z3,z4,z5,z811]),(0,[z2,z3,z4,z20,z8,z331]),(0,[z30,z1,z256,z4,z5,z6])],[],[(0,[z1,z2,z3,z4,z71,z6]),(0,[z232,z2,z79,z3,z4,z20]),(0,[z1,z222,z510,z4,z5,z6]),(0,[z1,z2,z3,z111,z6,z15]),(0,[z361,z2,z3,z4,z317,z6])],[(0,[z107,z2,z3,z53,z5,z330]),(0,[z1,z2,z79,z3,z4,z331]),(0,[z812,z2,z3,z4,z5,z6]),(0,[z813,z2,z3,z4,z5,z6])],[(0,[z17,z294,z3,z4,z5,z6]),(0,[z2,z3,z814,z4,z5,z6]),(0,[z676,z2,z3,z4,z8,z6]),(0,[z1,z223,z3,z4,z20,z6]),(0,[z1,z129,z3,z4,z82,z6]),(0,[z1,z3,z4,z718,z5,z6])],[(0,[z1,z2,z3,z4,z815,z6]),(0,[z1,z146,z31,z4,z8,z6]),(0,[z1,z129,z87,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z816]),(0,[z1,z2,z3,z4,z817,z6])],[(0,[z84,z2,z85,z4,z5,z6]),(0,[z1,z2,z3,z4,z818,z6]),(0,[z2,z3,z4,z752,z5,z6]),(0,[z1,z2,z819,z4,z5,z6]),(1,[z1,z223,z123,z5,z6]),(0,[z1,z3,z4,z5,z820,z6])]],
   [[(0,[z1,z2,z290,z4,z82,z6]),(1,[z1,z2,z821,z3,z5]),(0,[z1,z2,z821,z3,z19,z5])],[(0,[z283,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z92,z5,z6]),(0,[z1,z2,z3,z4,z822,z6])],[(0,[z97,z2,z3,z4,z8,z6]),(0,[z2,z3,z4,z8,z6,z567]),(0,[z1,z2,z3,z823,z5,z6])],[(0,[z696,z2,z3,z4,z8,z6]),(0,[z1,z2,z824,z3,z4,z6]),(0,[z1,z825,z2,z3,z4,z5]),(0,[z1,z2,z3,z826,z5,z6])],[(0,[z1,z2,z3,z4,z827,z6]),(0,[z1,z2,z3,z4,z5,z330]),(0,[z1,z2,z3,z4,z5,z331]),(0,[z1,z2,z152,z434,z4,z6]),(0,[z149,z1,z2,z47,z3,z4])],[(0,[z1,z2,z3,z138,z375,z6]),(0,[z1,z2,z3,z4,z255,z28])],[(0,[z81,z2,z3,z54,z218,z6]),(0,[z2,z79,z3,z4,z20,z8]),(0,[z1,z2,z3,z4,z828,z6]),(0,[z1,z2,z3,z4,z829,z6]),(0,[z1,z2,z830,z3,z4,z6])],[(0,[z17,z707,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z20,z831]),(0,[z97,z2,z3,z138,z5,z122]),(0,[z1,z2,z3,z4,z832,z6])]],
   [[(0,[z81,z2,z3,z54,z20,z6]),(0,[z1,z2,z3,z4,z5,z344]),(0,[z361,z2,z3,z111,z4,z6]),(0,[z149,z1,z2,z47,z3,z92])],[(0,[z1,z2,z833,z4,z5,z6]),(0,[z1,z2,z834,z4,z5,z6]),(0,[z1,z99,z508,z90,z5,z6]),(0,[z1,z223,z63,z3,z5,z6])],[(0,[z1,z2,z3,z4,z20,z835])],[(0,[z1,z2,z3,z836,z5,z6])],[(0,[z33,z1,z3,z4,z5,z293])],[(0,[z58,z18,z3,z4,z5,z6]),(0,[z1,z707,z3,z4,z5,z6]),(0,[z1,z2,z3,z837,z5,z6]),(0,[z97,z2,z3,z4,z20,z122]),(0,[z1,z2,z3,z838,z4,z6]),(0,[z1,z129,z510,z4,z5,z6]),(0,[z1,z839,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z840,z6]),(0,[z1,z2,z3,z4,z841,z6])],[(0,[z1,z2,z128,z290,z4,z5]),(0,[z309,z2,z3,z54,z5,z6]),(0,[z1,z2,z3,z284,z20,z6]),(0,[z1,z2,z3,z4,z842,z6]),(0,[z1,z223,z123,z5,z9,z6]),(0,[z843,z2,z3,z4,z5,z6]),(0,[z1,z2,z68,z761,z4,z5]),(0,[z1,z2,z844,z3,z4,z27])],[(0,[z1,z2,z276,z198,z3,z6])]],
   [[(0,[z593,z2,z3,z4,z8,z6]),(0,[z1,z2,z385,z327,z3,z6]),(0,[z1,z3,z4,z5,z130,z6])],[(0,[z1,z2,z3,z4,z5,z845]),(0,[z846,z2,z3,z4,z5,z6]),(0,[z847,z2,z3,z4,z5,z6])],[(0,[z1,z2,z205,z3,z8,z6]),(0,[z1,z223,z64,z4,z5,z6]),(0,[z1,z2,z3,z4,z848,z6]),(0,[z1,z2,z3,z19,z5,z159])],[(0,[z1,z849,z2,z3,z4,z5]),(0,[z1,z2,z510,z4,z8,z6]),(0,[z30,z1,z205,z37,z5,z6])],[(0,[z1,z2,z3,z4,z165,z6]),(0,[z538,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z45,z4,z331])],[(0,[z97,z2,z3,z4,z8,z207]),(0,[z1,z2,z172,z3,z4,z6]),(0,[z1,z2,z3,z4,z850,z6]),(0,[z1,z31,z769,z4,z5,z6]),(0,[z1,z99,z508,z3,z5,z6])],[(0,[z1,z2,z3,z4,z851,z6]),(0,[z127,z1,z2,z128,z4,z5]),(0,[z1,z2,z295,z3,z852,z4]),(0,[z1,z2,z853,z3,z4,z6])],[(0,[z97,z222,z3,z4,z8,z6]),(0,[z1,z2,z854,z3,z4,z6]),(0,[z2,z3,z4,z82,z8,z6]),(0,[z1,z61,z3,z4,z199,z6]),(0,[z297,z2,z3,z4,z20,z6]),(0,[z1,z2,z172,z147,z3,z6]),(0,[z1,z3,z100,z5,z555,z6]),(0,[z855,z2,z3,z4,z5,z6]),(0,[z856,z2,z3,z4,z5,z6])]],
   [[(0,[z97,z39,z2,z3,z4,z8]),(0,[z1,z2,z3,z761,z4,z5])],[(0,[z1,z2,z3,z857,z5,z6]),(0,[z127,z1,z2,z96,z4,z5])],[(0,[z1,z2,z3,z4,z858,z6])],[(0,[z1,z2,z3,z4,z8,z859]),(0,[z1,z73,z3,z100,z5,z6]),(0,[z1,z3,z718,z90,z5,z6])],[(0,[z1,z860,z2,z3,z4,z5]),(0,[z1,z99,z3,z465,z90,z6]),(0,[z86,z1,z2,z87,z3,z5])],[(0,[z1,z2,z3,z4,z861,z6]),(0,[z1,z2,z49,z434,z4,z6]),(0,[z1,z31,z4,z5,z390,z6]),(0,[z1,z2,z3,z111,z570,z6])],[(0,[z1,z2,z3,z862,z5,z6]),(0,[z2,z3,z4,z20,z752,z6]),(0,[z1,z36,z3,z4,z322,z6]),(0,[z1,z2,z3,z863,z4,z6]),(0,[z1,z2,z864,z3,z4,z6]),(0,[z1,z61,z3,z4,z220,z6]),(0,[z1,z2,z3,z865,z5,z6]),(0,[z1,z2,z3,z4,z158,z6]),(0,[z1,z866,z3,z4,z5,z6]),(0,[z1,z2,z3,z731,z4,z6])],[(0,[z1,z2,z3,z867,z5,z6]),(0,[z1,z868,z3,z4,z5,z6]),(0,[z1,z869,z3,z4,z5,z6]),(1,[z1,z99,z508,z5,z6])]],
   [[(0,[z97,z2,z3,z4,z267,z6]),(0,[z1,z2,z290,z379,z5,z6]),(0,[z46,z2,z3,z4,z255,z171]),(0,[z30,z1,z769,z4,z5,z6])],[(0,[z84,z2,z735,z4,z5,z6]),(0,[z116,z2,z187,z4,z20,z6]),(0,[z1,z2,z3,z4,z778,z6]),(0,[z299,z2,z3,z4,z8,z171]),(0,[z30,z1,z37,z4,z8,z6]),(0,[z46,z2,z3,z4,z5,z794]),(0,[z1,z2,z3,z4,z5,z217]),(0,[z1,z2,z155,z198,z3,z6])],[(0,[z664,z2,z187,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z870])],[(0,[z1,z2,z3,z379,z8,z6]),(0,[z871,z1,z2,z3,z4,z5]),(0,[z164,z2,z47,z3,z4,z5])],[(0,[z1,z389,z3,z4,z5,z76]),(0,[z1,z2,z3,z872,z5,z6]),(0,[z1,z2,z295,z3,z4,z873]),(0,[z232,z2,z3,z4,z20,z6]),(0,[z1,z2,z3,z4,z20,z573]),(0,[z1,z2,z79,z3,z4,z28])],[(0,[z1,z2,z3,z4,z874,z6])],[(0,[z1,z2,z875,z4,z5,z6]),(0,[z1,z2,z3,z876,z5,z6]),(0,[z84,z2,z85,z4,z260,z6])],[(0,[z1,z2,z3,z4,z218,z6]),(1,[z1,z3,z4,z5,z709])]],
   [[(0,[z1,z2,z147,z3,z5,z6])],[(0,[z1,z877,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z878,z5]),(0,[z97,z129,z3,z4,z8,z6])],[(0,[z1,z879,z2,z3,z4,z5]),(0,[z1,z880,z3,z4,z5,z6]),(0,[z1,z39,z3,z4,z8,z76]),(1,[z1,z3,z718,z5,z6]),(0,[z1,z2,z3,z4,z27,z28])],[(0,[z2,z3,z4,z8,z644,z6]),(0,[z1,z2,z41,z4,z564,z6]),(0,[z1,z2,z47,z3,z4,z331]),(0,[z1,z2,z3,z4,z881,z6]),(0,[z149,z361,z2,z47,z3,z4])],[(0,[z1,z2,z3,z882,z4,z6]),(0,[z84,z2,z85,z4,z8,z6]),(0,[z2,z3,z4,z752,z8,z6]),(0,[z97,z2,z290,z4,z8,z6]),(0,[z1,z2,z123,z8,z9,z6])],[(0,[z17,z294,z3,z4,z71,z6]),(0,[z1,z2,z3,z814,z5,z6]),(0,[z1,z2,z3,z4,z883,z6]),(0,[z664,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z379,z5,z159]),(0,[z1,z2,z3,z884,z5,z6]),(0,[z1,z2,z51,z87,z3,z5])],[(0,[z1,z2,z885,z3,z5,z6]),(0,[z107,z2,z295,z3,z53,z5]),(0,[z1,z2,z3,z138,z82,z6]),(0,[z1,z2,z3,z111,z11,z6])],[(0,[z1,z2,z3,z4,z886,z6]),(0,[z1,z39,z129,z3,z4,z5]),(0,[z1,z2,z887,z3,z4,z6]),(0,[z1,z888,z3,z4,z5,z6]),(0,[z1,z889,z2,z3,z4,z5])]],
   [[(0,[z1,z2,z41,z190,z4,z6])],[(0,[z97,z2,z68,z3,z4,z8]),(0,[z30,z1,z2,z205,z5,z6]),(0,[z1,z2,z89,z4,z5,z6]),(0,[z164,z2,z3,z4,z5,z28]),(0,[z1,z2,z47,z844,z3,z4])],[(0,[z1,z2,z3,z4,z890,z6]),(0,[z891,z2,z3,z4,z5,z6]),(0,[z1,z2,z41,z4,z65,z6]),(0,[z1,z2,z3,z4,z5,z892])],[(0,[z107,z2,z3,z53,z8,z6]),(0,[z1,z2,z893,z4,z5,z6]),(0,[z33,z1,z129,z3,z4,z5]),(0,[z1,z2,z49,z42,z4,z6]),(0,[z1,z2,z3,z4,z894,z6]),(0,[z361,z2,z3,z4,z27,z6])],[(0,[z1,z2,z895,z3,z4,z5]),(0,[z1,z2,z3,z4,z896,z6]),(0,[z397,z2,z3,z4,z8,z6]),(0,[z97,z2,z3,z4,z82,z122]),(0,[z1,z2,z3,z4,z897,z6]),(0,[z1,z2,z3,z111,z6,z112])],[(0,[z1,z2,z3,z4,z898,z6]),(0,[z1,z129,z3,z4,z5,z6]),(0,[z1,z2,z899,z3,z4,z6]),(0,[z900,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z901,z5,z6])],[(0,[z1,z2,z3,z4,z20,z902])],[(0,[z1,z903,z3,z4,z5,z6]),(0,[z30,z1,z124,z37,z4,z6]),(0,[z1,z2,z205,z172,z3,z6]),(0,[z1,z2,z3,z465,z4,z6])]],
   [[(0,[z1,z2,z290,z4,z5,z6])],[(0,[z1,z2,z3,z904,z4,z6]),(0,[z1,z2,z3,z4,z905,z6])],[(0,[z1,z2,z3,z4,z5,z748]),(0,[z97,z2,z3,z4,z5,z794]),(0,[z1,z2,z3,z906,z5,z6])],[(0,[z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z907,z6]),(0,[z1,z2,z908,z4,z5,z6]),(0,[z1,z3,z769,z4,z5,z6])],[(0,[z1,z2,z3,z4,z351,z6]),(0,[z1,z2,z909,z4,z5,z6]),(0,[z1,z2,z3,z4,z910,z6]),(0,[z1,z2,z3,z4,z911,z6]),(0,[z341,z2,z3,z4,z20,z6]),(0,[z30,z1,z205,z3,z5,z6]),(0,[z1,z2,z123,z5,z573,z9]),(0,[z1,z912,z2,z3,z4,z5]),(0,[z1,z2,z63,z823,z5,z6])],[(0,[z1,z99,z3,z586,z5,z6]),(0,[z1,z2,z3,z4,z764,z6]),(0,[z1,z2,z913,z3,z4,z5]),(0,[z149,z1,z2,z47,z3,z284])],[(0,[z1,z2,z3,z914,z5,z6]),(0,[z1,z2,z510,z138,z5,z6]),(0,[z2,z3,z4,z5,z6,z915]),(0,[z1,z2,z3,z4,z5,z916]),(0,[z1,z2,z3,z4,z5,z917])],[(0,[z1,z2,z3,z918,z5,z6]),(0,[z1,z2,z735,z4,z5,z6]),(0,[z1,z2,z3,z19,z8,z159]),(0,[z1,z299,z2,z47,z3,z4]),(1,[z1,z2,z823,z5,z6]),(0,[z1,z2,z821,z3,z5,z159])]],
   [[(0,[z1,z2,z3,z4,z5,z919]),(0,[z164,z2,z3,z4,z8,z6]),(0,[z1,z2,z920,z3,z4,z6]),(0,[z127,z1,z2,z315,z4,z5])],[(0,[z1,z2,z921,z4,z5,z6]),(0,[z1,z357,z3,z4,z5,z56])],[(0,[z1,z2,z3,z4,z67,z6]),(0,[z1,z2,z3,z4,z873,z6]),(0,[z1,z2,z922,z3,z4,z6]),(0,[z1,z2,z41,z4,z668,z6])],[(0,[z1,z923,z3,z4,z5,z6]),(0,[z1,z2,z79,z3,z4,z20]),(0,[z1,z2,z3,z4,z924,z6]),(0,[z2,z3,z4,z8,z262,z6]),(0,[z1,z2,z205,z3,z20,z6]),(0,[z30,z1,z172,z37,z4,z6]),(0,[z1,z2,z844,z3,z4,z6])],[(0,[z2,z253,z3,z4,z8,z6]),(0,[z97,z2,z3,z4,z5,z602]),(0,[z1,z2,z510,z4,z20,z6]),(0,[z30,z1,z461,z4,z5,z6]),(0,[z1,z2,z3,z4,z925,z6]),(0,[z164,z149,z2,z47,z3,z4])],[(0,[z58,z707,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z926,z6]),(0,[z97,z2,z47,z3,z4,z8]),(0,[z46,z696,z2,z3,z4,z5]),(0,[z1,z2,z3,z927,z5,z6])],[(0,[z1,z2,z3,z4,z928,z6]),(0,[z2,z3,z4,z5,z6,z929]),(0,[z1,z2,z930,z3,z4,z5]),(0,[z1,z2,z68,z4,z5,z69]),(0,[z1,z2,z3,z111,z649,z6])],[(0,[z1,z2,z931,z4,z5,z6]),(0,[z1,z879,z2,z3,z4,z8]),(0,[z46,z2,z3,z4,z5,z171])]],
   [[(0,[z1,z3,z4,z5,z932,z6]),(0,[z1,z933,z3,z4,z5,z6]),(0,[z1,z73,z3,z100,z8,z6]),(0,[z934,z2,z3,z4,z5,z6]),(0,[z1,z99,z3,z90,z5,z6]),(0,[z1,z2,z3,z4,z935,z6]),(0,[z1,z2,z3,z731,z111,z6])],[(0,[z1,z2,z3,z4,z936,z6]),(0,[z2,z79,z3,z4,z8,z6]),(0,[z1,z2,z508,z4,z5,z6]),(0,[z1,z166,z2,z123,z5,z6]),(0,[z2,z3,z4,z5,z6,z937]),(0,[z1,z2,z14,z494,z3,z6])],[(0,[z1,z2,z3,z4,z938,z6]),(0,[z33,z1,z3,z4,z8,z56]),(0,[z1,z2,z3,z26,z6,z159])],[(0,[z1,z2,z3,z4,z939,z6]),(0,[z1,z2,z940,z3,z4,z6]),(0,[z1,z2,z3,z862,z8,z6]),(0,[z1,z2,z410,z4,z65,z6])],[(0,[z1,z941,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z942,z5]),(0,[z2,z281,z3,z4,z8,z6]),(0,[z1,z2,z3,z943,z4,z6]),(0,[z86,z1,z2,z87,z3,z26])],[(0,[z1,z2,z3,z944,z4,z6]),(0,[z191,z2,z3,z4,z8,z6]),(0,[z1,z222,z290,z4,z5,z6]),(0,[z1,z2,z3,z945,z4,z6]),(0,[z1,z48,z632,z3,z4,z6]),(0,[z1,z2,z3,z4,z946,z6]),(0,[z1,z3,z4,z5,z56,z709])],[(0,[z1,z2,z947,z4,z5,z6]),(0,[z1,z2,z3,z4,z8,z217]),(0,[z97,z2,z3,z4,z375,z122]),(0,[z1,z2,z123,z158,z9,z6])],[(0,[z1,z2,z79,z3,z4,z8])]],
   [[(0,[z1,z2,z3,z4,z948,z6]),(0,[z1,z222,z3,z4,z8,z6]),(0,[z278,z2,z3,z4,z8,z6]),(0,[z949,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z950,z5,z6])],[(0,[z1,z2,z3,z4,z951,z6]),(0,[z1,z2,z410,z4,z488,z6]),(0,[z127,z1,z2,z315,z4,z20]),(0,[z97,z2,z281,z3,z4,z5])],[(0,[z30,z1,z37,z4,z20,z6]),(0,[z2,z3,z119,z4,z20,z6]),(0,[z1,z2,z3,z379,z375,z6]),(0,[z1,z99,z377,z3,z5,z6]),(0,[z952,z2,z3,z4,z5,z6])],[(0,[z84,z2,z128,z85,z4,z5]),(0,[z953,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z954])],[(0,[z1,z299,z2,z208,z3,z4]),(0,[z1,z2,z3,z379,z20,z6]),(0,[z97,z2,z3,z379,z5,z122]),(0,[z1,z223,z123,z3,z5,z6])],[(0,[z1,z955,z3,z4,z5,z6]),(0,[z1,z2,z3,z956,z5,z6]),(1,[z1,z2,z761,z4,z5]),(0,[z86,z1,z2,z87,z3,z500])],[(0,[z60,z2,z3,z4,z752,z6]),(0,[z30,z1,z147,z37,z5,z6])],[(0,[z1,z2,z3,z4,z5,z957]),(0,[z1,z2,z3,z958,z4,z5]),(0,[z1,z2,z3,z4,z5,z959]),(0,[z1,z99,z520,z3,z90,z6]),(0,[z1,z2,z3,z960,z5,z6]),(0,[z1,z2,z3,z111,z421,z6])]],
   [[(0,[z1,z2,z961,z3,z4,z6]),(0,[z1,z2,z962,z3,z4,z6]),(0,[z1,z963,z3,z4,z5,z6])],[(0,[z107,z2,z3,z53,z237,z6]),(1,[z2,z3,z4,z752,z6]),(0,[z1,z2,z3,z4,z8,z257]),(0,[z1,z2,z3,z4,z267,z6])],[(0,[z1,z2,z3,z964,z5,z6]),(0,[z1,z2,z3,z4,z965,z6]),(0,[z2,z3,z4,z317,z8,z6]),(0,[z97,z2,z3,z138,z8,z6]),(0,[z1,z2,z63,z64,z8,z6]),(0,[z1,z205,z31,z3,z5,z6]),(0,[z1,z2,z761,z4,z5,z6])],[(0,[z1,z389,z2,z3,z4,z5]),(0,[z1,z2,z966,z4,z5,z6]),(0,[z107,z2,z3,z814,z5,z6]),(0,[z1,z2,z885,z3,z8,z6]),(0,[z1,z39,z3,z4,z20,z76]),(0,[z1,z2,z298,z315,z4,z5])],[(0,[z1,z2,z3,z787,z8,z6]),(0,[z1,z2,z3,z717,z5,z6]),(0,[z1,z223,z3,z4,z5,z6]),(0,[z361,z2,z47,z3,z4,z6])],[(0,[z84,z2,z85,z4,z20,z6]),(0,[z127,z1,z2,z315,z4,z8]),(0,[z232,z2,z3,z4,z20,z331]),(0,[z1,z2,z3,z4,z942,z20]),(0,[z1,z2,z276,z3,z4,z331]),(0,[z1,z2,z3,z967,z4,z6]),(0,[z1,z2,z968,z4,z5,z6]),(0,[z1,z61,z265,z3,z4,z6])],[(0,[z1,z2,z123,z20,z9,z6]),(0,[z1,z2,z3,z4,z969,z6])],[(0,[z1,z2,z3,z970,z4,z5]),(0,[z1,z2,z3,z4,z5,z971]),(0,[z2,z3,z4,z8,z354,z6]),(0,[z1,z129,z290,z4,z5,z6]),(0,[z1,z99,z508,z4,z5,z6]),(0,[z1,z2,z3,z4,z972,z6])]],
   [[(0,[z1,z2,z3,z4,z973,z6]),(0,[z58,z389,z18,z3,z4,z5]),(0,[z1,z974,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z975,z6]),(0,[z1,z146,z769,z4,z5,z6]),(0,[z976,z2,z3,z4,z5,z6])],[(0,[z1,z977,z3,z4,z5,z6]),(0,[z84,z487,z2,z85,z4,z5]),(0,[z1,z2,z3,z4,z237,z6]),(0,[z2,z3,z4,z8,z6,z126]),(0,[z1,z2,z3,z4,z978,z6])],[(0,[z1,z2,z979,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z980]),(0,[z1,z129,z3,z4,z8,z6]),(0,[z306,z2,z3,z4,z8,z6]),(0,[z490,z2,z3,z4,z20,z6]),(0,[z1,z2,z981,z4,z5,z6])],[(0,[z1,z2,z3,z4,z982,z6]),(0,[z97,z2,z3,z4,z8,z28]),(0,[z1,z73,z2,z508,z5,z6])],[(0,[z84,z2,z85,z4,z452,z6]),(0,[z107,z2,z3,z53,z20,z6]),(0,[z1,z2,z983,z3,z4,z6]),(0,[z1,z2,z797,z3,z8,z6]),(0,[z1,z2,z3,z984,z20,z6]),(0,[z46,z480,z2,z3,z4,z5]),(1,[z1,z2,z844,z3,z4])],[(0,[z1,z2,z3,z985,z5,z6]),(0,[z2,z79,z3,z4,z5,z8]),(0,[z2,z398,z3,z4,z20,z6])],[(0,[z1,z2,z3,z4,z5,z986]),(0,[z1,z2,z3,z4,z5,z831]),(0,[z1,z2,z3,z138,z5,z6]),(0,[z1,z2,z3,z987,z5,z6]),(0,[z1,z99,z3,z90,z5,z257])],[]],
   [[(0,[z1,z2,z988,z3,z4,z5]),(0,[z2,z735,z85,z4,z5,z6]),(0,[z1,z2,z3,z4,z989,z6]),(0,[z1,z2,z3,z958,z4,z20]),(0,[z1,z2,z3,z4,z5,z990]),(0,[z1,z2,z991,z4,z5,z6]),(0,[z1,z2,z14,z3,z731,z6])],[(0,[z1,z2,z3,z4,z5,z835]),(0,[z1,z2,z3,z4,z8,z811]),(0,[z1,z334,z3,z4,z5,z76]),(0,[z361,z2,z14,z3,z4,z6])],[(0,[z1,z2,z3,z681,z5,z159]),(0,[z2,z3,z53,z814,z5,z6]),(0,[z2,z3,z4,z8,z6,z160]),(0,[z2,z3,z4,z8,z6,z161]),(0,[z1,z2,z3,z201,z5,z159]),(0,[z992,z1,z2,z3,z4,z5])],[(0,[z1,z2,z993,z3,z5,z6]),(0,[z1,z2,z994,z3,z4,z6]),(0,[z1,z2,z79,z3,z4,z82]),(0,[z1,z2,z205,z3,z5,z995])],[(0,[z1,z2,z3,z4,z20,z6]),(0,[z1,z389,z2,z3,z4,z20]),(0,[z97,z2,z3,z4,z5,z122]),(0,[z1,z2,z3,z4,z996,z6]),(0,[z1,z997,z2,z3,z4,z5]),(0,[z1,z223,z3,z4,z158,z6])],[(0,[z17,z294,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z998,z6]),(0,[z1,z2,z3,z363,z5,z159]),(0,[z1,z2,z3,z284,z5,z6])],[(0,[z1,z2,z3,z4,z999,z6]),(0,[z1,z2,z87,z290,z4,z5]),(0,[z1,z2,z1000,z3,z4,z6])],[(0,[z1,z2,z3,z4,z1001,z6]),(0,[z1,z2,z844,z3,z4,z5])]],
   [[(0,[z1,z2,z128,z4,z5,z69]),(0,[z1,z2,z276,z347,z3,z6]),(0,[z1,z2,z3,z19,z20,z159])],[(0,[z1,z2,z3,z4,z5,z724]),(0,[z1,z2,z1002,z3,z4,z5]),(0,[z1,z2,z3,z92,z8,z6]),(0,[z164,z2,z3,z4,z20,z6]),(0,[z97,z2,z523,z3,z4,z5]),(0,[z1,z146,z2,z205,z5,z6]),(0,[z1,z2,z3,z628,z5,z159])],[(0,[z550,z294,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z8,z6]),(0,[z1,z146,z31,z4,z20,z6]),(0,[z1003,z2,z3,z4,z5,z6]),(0,[z30,z1,z466,z4,z5,z6]),(0,[z1,z2,z520,z3,z4,z6]),(0,[z1,z2,z1004,z3,z4,z6]),(0,[z1,z2,z3,z4,z1005,z6])],[(0,[z1,z2,z3,z4,z452,z6]),(0,[z1,z849,z2,z3,z4,z8]),(0,[z1,z2,z68,z4,z8,z69]),(0,[z1,z2,z3,z4,z5,z794]),(0,[z1,z2,z1006,z4,z5,z6]),(0,[z1,z48,z3,z4,z55,z6]),(0,[z1,z296,z2,z87,z3,z5])],[(0,[z1,z2,z3,z4,z1007,z6]),(0,[z33,z1,z389,z3,z4,z5]),(0,[z81,z2,z3,z814,z5,z6]),(0,[z1,z2,z3,z4,z8,z330]),(0,[z1,z2,z3,z4,z8,z331]),(0,[z1,z2,z3,z4,z1008,z6])],[],[(0,[z1,z2,z771,z4,z5,z6]),(0,[z1,z2,z3,z4,z1009,z6])],[(0,[z1,z2,z1010,z4,z5,z6]),(0,[z1,z2,z128,z3,z4,z5]),(0,[z1,z2,z3,z4,z1011,z6]),(0,[z86,z1,z2,z295,z3,z5]),(0,[z1,z2,z3,z4,z20,z741])]],
   [[(0,[z1,z389,z2,z3,z4,z8]),(0,[z1,z2,z3,z4,z8,z344]),(0,[z361,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1012])],[(0,[z1,z2,z3,z4,z1013,z6]),(0,[z1,z73,z3,z100,z20,z6])],[(0,[z1,z2,z205,z3,z1014,z5])],[(0,[z1,z2,z3,z4,z5,z1015]),(0,[z1,z2,z295,z3,z5,z159]),(0,[z1,z2,z3,z4,z35,z207]),(0,[z33,z1,z3,z4,z20,z56]),(0,[z1,z222,z3,z138,z5,z6]),(0,[z1,z2,z3,z379,z82,z6])],[(0,[z1,z2,z3,z4,z5,z1016]),(0,[z1,z2,z3,z4,z1017,z6]),(0,[z1,z2,z3,z4,z1018,z6]),(0,[z97,z2,z3,z4,z8,z159])],[(0,[z58,z18,z3,z4,z8,z6]),(0,[z1,z2,z295,z3,z379,z5]),(0,[z1,z2,z3,z837,z8,z6]),(0,[z1,z2,z87,z3,z379,z5]),(0,[z1,z2,z123,z5,z9,z6])],[(0,[z280,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z1019,z6])],[(0,[z1,z2,z3,z4,z20,z217]),(0,[z1,z2,z3,z45,z6,z438])]],
   [[(0,[z46,z2,z3,z4,z5,z160]),(0,[z46,z2,z3,z4,z5,z161]),(0,[z1,z99,z2,z508,z5,z6])],[(0,[z97,z2,z208,z3,z4,z8]),(0,[z1,z222,z3,z4,z20,z6]),(0,[z97,z222,z3,z4,z5,z122]),(0,[z1,z2,z3,z4,z1020,z6]),(0,[z1,z40,z3,z4,z130,z6])],[(0,[z1,z2,z79,z3,z984,z5]),(0,[z127,z1,z2,z300,z4,z5]),(0,[z1,z2,z3,z4,z1021,z6]),(0,[z1,z73,z3,z718,z5,z6]),(0,[z1,z2,z3,z4,z1022,z6])],[(0,[z1,z3,z4,z764,z5,z6]),(0,[z1,z2,z4,z728,z5,z6])],[(0,[z58,z18,z3,z4,z67,z6]),(0,[z1,z2,z3,z4,z1023,z6]),(0,[z1024,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z1025,z6]),(0,[z1,z487,z2,z3,z4,z5]),(0,[z1,z2,z510,z4,z375,z6]),(0,[z2,z3,z4,z5,z171,z794]),(0,[z1,z99,z3,z90,z5,z344]),(0,[z1,z223,z40,z3,z4,z6]),(0,[z1,z1026,z3,z4,z5,z6])],[(0,[z1,z2,z1027,z3,z4,z6]),(0,[z30,z1,z205,z4,z5,z6]),(0,[z1,z2,z769,z4,z5,z6]),(0,[z1,z3,z100,z718,z5,z6]),(0,[z1,z2,z87,z821,z3,z5])],[(0,[z1,z2,z3,z749,z4,z5]),(0,[z1,z2,z3,z4,z317,z331]),(0,[z1,z2,z79,z3,z805,z5]),(0,[z97,z2,z510,z4,z5,z122]),(0,[z1,z2,z3,z1028,z5,z6]),(0,[z1,z2,z123,z823,z5,z6])]],
   [[(0,[z1,z2,z128,z3,z4,z20]),(0,[z551,z2,z3,z4,z8,z6]),(0,[z2,z441,z3,z4,z8,z6]),(0,[z46,z1,z2,z3,z284,z5])],[(0,[z1,z2,z3,z1029,z4,z6]),(0,[z1,z2,z3,z4,z878,z8]),(0,[z1030,z2,z3,z4,z5,z6])],[(1,[z707,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z20,z257]),(0,[z86,z1,z2,z3,z694,z5]),(0,[z1031,z2,z3,z4,z5,z6])],[(0,[z2,z707,z3,z4,z5,z6]),(0,[z1,z2,z63,z64,z20,z6]),(0,[z2,z3,z319,z4,z20,z6]),(0,[z1,z2,z510,z379,z5,z6]),(0,[z1,z2,z1032,z3,z4,z6])],[(0,[z1,z1033,z3,z4,z5,z6]),(0,[z2,z3,z4,z8,z171,z6]),(0,[z1034,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z1035,z4,z6]),(0,[z1,z129,z3,z138,z5,z6])],[(0,[z1,z2,z1036,z3,z4,z6]),(0,[z232,z2,z3,z4,z82,z6]),(0,[z1,z2,z3,z1037,z5,z6])],[(0,[z1,z2,z123,z461,z5,z6]),(0,[z1,z2,z3,z4,z1038,z6])]],
   [[(0,[z1,z1039,z3,z4,z5,z6]),(0,[z1,z2,z290,z138,z5,z6])],[(0,[z1,z2,z3,z359,z6,z189]),(0,[z97,z2,z135,z3,z4,z5])],[(0,[z1,z2,z1040,z3,z4,z6]),(0,[z1,z2,z3,z4,z1041,z6]),(0,[z86,z1,z2,z821,z3,z5])],[(0,[z1,z2,z3,z4,z82,z6]),(0,[z1,z2,z3,z138,z8,z6]),(0,[z1,z129,z3,z4,z20,z6]),(0,[z1,z2,z79,z3,z984,z20]),(0,[z1,z2,z3,z4,z1042,z6]),(0,[z1,z2,z1043,z3,z4,z6])],[(0,[z1,z2,z128,z3,z4,z8]),(0,[z1,z2,z3,z4,z1044,z6]),(0,[z1,z2,z295,z3,z4,z5]),(0,[z232,z2,z3,z4,z752,z6]),(0,[z1,z2,z3,z111,z4,z331]),(0,[z1,z2,z3,z4,z5,z995]),(0,[z1,z2,z14,z3,z365,z6])],[(0,[z1,z2,z3,z4,z5,z902]),(0,[z2,z187,z735,z4,z5,z6]),(0,[z2,z3,z814,z54,z5,z6]),(0,[z1,z2,z3,z4,z5,z1045])],[(0,[z1,z487,z2,z3,z4,z20]),(0,[z1,z1046,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1047,z6])],[(0,[z10,z2,z3,z4,z20,z6]),(0,[z1,z2,z3,z4,z1048,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z1049]),(0,[z1,z2,z1050,z3,z4,z6]),(0,[z2,z3,z4,z778,z8,z6]),(0,[z1,z2,z147,z3,z8,z6]),(0,[z1,z2,z79,z3,z805,z20]),(0,[z1,z2,z3,z805,z20,z6]),(0,[z164,z2,z3,z4,z82,z6]),(0,[z1,z73,z499,z3,z5,z6]),(0,[z1,z2,z3,z4,z1051,z6])],[(0,[z1,z389,z129,z3,z4,z5]),(0,[z480,z2,z3,z4,z8,z6]),(0,[z1,z877,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z1052,z6]),(0,[z1,z2,z3,z284,z8,z6]),(0,[z1,z2,z3,z4,z20,z810]),(0,[z1,z2,z47,z3,z4,z82]),(0,[z1,z2,z3,z1053,z4,z6]),(0,[z86,z1,z2,z3,z26,z6])],[(0,[z707,z18,z3,z4,z5,z6]),(0,[z1,z2,z3,z1054,z4,z5]),(1,[z1,z3,z4,z764,z6]),(0,[z1,z1055,z3,z4,z5,z6]),(0,[z1,z2,z42,z4,z728,z6]),(0,[z1,z2,z821,z3,z4,z5])],[(0,[z1,z146,z515,z4,z5,z6])],[(0,[z1,z2,z315,z761,z4,z5])],[(0,[z17,z294,z3,z4,z20,z6]),(0,[z1,z2,z3,z4,z5,z715]),(0,[z1,z2,z1056,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z1057]),(0,[z1,z223,z123,z4,z5,z6]),(0,[z1058,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1059]),(0,[z2,z3,z4,z5,z6,z794]),(0,[z1,z99,z3,z718,z5,z6]),(0,[z1,z61,z3,z4,z764,z6]),(0,[z1,z223,z2,z123,z5,z6])]],
   [[(0,[z1,z2,z14,z327,z3,z6])],[(0,[z1,z2,z3,z1060,z5,z6]),(0,[z1,z2,z89,z4,z8,z6]),(0,[z97,z1,z2,z3,z284,z5]),(0,[z2,z3,z4,z267,z171,z6])],[(0,[z1,z487,z2,z3,z4,z8]),(0,[z2,z542,z3,z4,z20,z6]),(0,[z2,z3,z4,z20,z185,z6]),(0,[z1,z2,z3,z92,z20,z6]),(0,[z1,z1061,z3,z4,z5,z6])],[(0,[z1,z2,z3,z1062,z4,z5]),(0,[z125,z2,z3,z4,z8,z6]),(0,[z1,z48,z3,z4,z21,z6]),(0,[z1063,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1014,z5]),(0,[z1,z2,z3,z4,z1064,z6]),(0,[z1065,z2,z3,z4,z5,z6])],[(0,[z1,z221,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z255,z6]),(0,[z1,z2,z68,z4,z20,z69]),(0,[z1,z99,z466,z3,z5,z6]),(0,[z1,z2,z3,z4,z1066,z6]),(0,[z1,z2,z844,z3,z4,z28])],[(0,[z1,z2,z3,z4,z20,z330]),(0,[z1,z2,z295,z3,z4,z20]),(0,[z1,z2,z3,z4,z20,z331]),(0,[z97,z33,z2,z3,z4,z8]),(0,[z361,z2,z3,z4,z8,z6]),(0,[z97,z2,z3,z4,z5,z207]),(0,[z1067,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1068]),(0,[z1,z2,z3,z4,z5,z1069]),(0,[z1,z2,z1070,z3,z4,z6])],[(0,[z1,z2,z3,z4,z1071,z6]),(0,[z1,z181,z3,z4,z77,z6]),(0,[z1,z2,z1072,z4,z5,z6]),(0,[z1,z48,z3,z4,z764,z6]),(0,[z1,z2,z14,z198,z3,z6])]],
   [[(0,[z1,z2,z1073,z4,z5,z6]),(0,[z1,z2,z1074,z4,z5,z6]),(0,[z1,z2,z290,z4,z8,z6]),(0,[z1,z222,z3,z4,z82,z6])],[(0,[z58,z221,z18,z3,z4,z5]),(0,[z1,z2,z3,z4,z20,z344]),(0,[z1,z2,z491,z4,z564,z6]),(0,[z1,z2,z1075,z3,z4,z6])],[(0,[z81,z2,z3,z54,z5,z6]),(1,[z2,z3,z814,z5,z6]),(0,[z1,z2,z3,z4,z5,z1076])],[(0,[z1,z2,z3,z4,z5,z859])],[(0,[z1,z2,z909,z4,z8,z6]),(0,[z1,z2,z123,z586,z5,z6]),(0,[z1,z2,z205,z124,z3,z6]),(0,[z1,z2,z1077,z3,z4,z6]),(0,[z1,z2,z123,z40,z9,z6]),(0,[z1,z2,z3,z4,z1078,z6])],[(0,[z1,z2,z1079,z3,z4,z5]),(0,[z1,z2,z3,z4,z375,z6])],[(0,[z58,z18,z3,z4,z20,z6]),(0,[z1,z2,z3,z1080,z5,z6]),(0,[z1,z2,z510,z4,z82,z6]),(0,[z1,z99,z89,z90,z5,z6]),(0,[z1,z2,z3,z1081,z5,z6]),(0,[z1,z2,z198,z3,z731,z6])],[(0,[z1,z129,z3,z4,z5,z159]),(0,[z2,z3,z4,z5,z794,z122]),(0,[z1,z2,z823,z5,z9,z6]),(0,[z1,z2,z370,z4,z5,z69]),(0,[z1,z2,z3,z26,z4,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z1082]),(0,[z1,z2,z3,z1083,z5,z6])],[(0,[z538,z2,z3,z53,z5,z6]),(0,[z299,z2,z3,z4,z5,z171])],[(0,[z1,z2,z290,z4,z5,z159]),(0,[z1,z2,z3,z4,z1084,z6]),(0,[z244,z1,z2,z3,z111,z6])],[(0,[z1,z2,z3,z379,z5,z6]),(0,[z97,z2,z384,z3,z4,z5]),(0,[z1,z2,z3,z4,z1085,z6])],[(0,[z1,z1086,z3,z4,z5,z6]),(0,[z1,z2,z3,z852,z4,z6]),(0,[z1,z3,z4,z8,z932,z6]),(0,[z1,z769,z37,z4,z5,z6]),(1,[z1,z2,z4,z728,z6])],[(0,[z1,z221,z2,z3,z4,z20]),(0,[z1,z2,z1087,z4,z5,z6]),(0,[z2,z3,z735,z4,z5,z6]),(0,[z1,z2,z3,z4,z1088,z6]),(0,[z81,z2,z3,z54,z121,z6]),(0,[z60,z2,z3,z4,z8,z6]),(0,[z1,z2,z214,z42,z4,z6]),(0,[z1,z48,z3,z630,z4,z6])],[(0,[z1,z2,z3,z4,z1089,z6]),(0,[z1,z2,z3,z4,z5,z1090]),(0,[z127,z1,z2,z290,z4,z5]),(0,[z1,z2,z3,z4,z5,z1091])],[(0,[z1,z1092,z3,z4,z5,z6]),(0,[z46,z2,z3,z4,z8,z171]),(0,[z1,z2,z3,z731,z5,z6])]],
   [[(0,[z1,z1093,z3,z4,z5,z6]),(0,[z1,z99,z3,z90,z8,z6]),(0,[z1,z2,z14,z3,z673,z6]),(0,[z1,z2,z64,z823,z5,z6])],[(0,[z1,z2,z3,z4,z1094,z6]),(0,[z1,z2,z508,z4,z8,z6]),(0,[z439,z2,z3,z4,z20,z6]),(0,[z2,z3,z4,z440,z20,z6])],[(0,[z1,z2,z3,z4,z1095,z6]),(0,[z514,z2,z3,z4,z8,z6]),(0,[z1,z2,z1096,z3,z5,z6]),(0,[z1,z39,z3,z4,z5,z76]),(0,[z1,z2,z3,z4,z728,z6]),(0,[z1,z2,z3,z597,z5,z159])],[(0,[z97,z2,z87,z3,z4,z8]),(0,[z46,z1,z2,z3,z4,z500]),(0,[z1,z2,z3,z4,z1097,z6]),(0,[z1,z2,z3,z4,z1098,z6]),(0,[z149,z1,z2,z3,z92,z6])],[(1,[z2,z735,z4,z5,z6]),(0,[z116,z2,z187,z4,z115,z6]),(0,[z1,z2,z988,z3,z4,z20]),(0,[z314,z2,z3,z4,z20,z6]),(0,[z1,z2,z3,z111,z6,z438]),(0,[z30,z1,z99,z123,z5,z6]),(0,[z1,z2,z3,z4,z1099,z6])],[(0,[z1,z2,z1100,z3,z4,z6]),(0,[z1,z2,z3,z4,z1101,z6]),(0,[z1,z2,z3,z4,z1102,z6]),(0,[z1,z61,z462,z3,z4,z6]),(0,[z1,z2,z3,z4,z1103,z6])],[(0,[z1,z2,z3,z4,z1104,z6]),(0,[z1,z2,z3,z4,z5,z1105]),(0,[z1,z1106,z2,z3,z4,z6]),(0,[z1,z2,z3,z731,z6,z15])],[(0,[z1,z3,z4,z8,z130,z6]),(0,[z1,z2,z3,z4,z27,z331]),(0,[z1,z2,z3,z4,z1107,z6]),(0,[z1,z2,z1108,z3,z5,z6]),(0,[z1,z2,z465,z89,z4,z6]),(0,[z1,z2,z3,z4,z1109,z6]),(0,[z1,z1110,z2,z3,z4,z5]),(0,[z1,z2,z49,z326,z4,z6])]],
   [[(0,[z2,z3,z4,z20,z8,z6]),(0,[z1,z2,z3,z1111,z4,z6]),(0,[z1,z2,z3,z4,z1112,z6]),(0,[z1,z2,z3,z4,z1113,z6])],[(0,[z58,z18,z3,z4,z351,z6]),(0,[z1,z221,z2,z3,z4,z8]),(0,[z1,z2,z1114,z4,z5,z6]),(0,[z368,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z1115,z6]),(0,[z1,z2,z3,z4,z1116,z6]),(0,[z1,z2,z3,z4,z1117,z6]),(0,[z1,z3,z4,z764,z55,z6]),(0,[z1,z2,z4,z823,z5,z6]),(0,[z1,z2,z3,z4,z1118,z6]),(0,[z149,z1,z2,z844,z3,z4])],[(0,[z1,z222,z3,z4,z375,z6])],[(0,[z116,z2,z187,z4,z5,z6]),(0,[z107,z2,z3,z53,z5,z6]),(0,[z1,z2,z3,z984,z5,z6]),(0,[z1,z2,z1119,z4,z5,z6])],[(0,[z1,z2,z3,z4,z114,z6]),(0,[z1,z2,z3,z4,z115,z6]),(0,[z1,z2,z1120,z3,z4,z6]),(0,[z1,z2,z3,z138,z20,z6])],[(0,[z1,z2,z3,z4,z1121,z6]),(0,[z1,z2,z3,z4,z1122,z6]),(0,[z1,z2,z3,z1123,z4,z6]),(0,[z1,z2,z821,z3,z5,z6])],[(0,[z97,z127,z2,z3,z4,z8]),(0,[z1,z2,z124,z3,z4,z6]),(0,[z1,z2,z63,z105,z5,z6]),(0,[z1,z2,z3,z4,z5,z573]),(0,[z1,z3,z4,z5,z1124,z6]),(0,[z1,z1125,z3,z4,z5,z6])],[(0,[z33,z1,z618,z3,z4,z5]),(0,[z1,z39,z3,z4,z5,z709])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 8 256 bkB c

def parents : List (ℕ × List W) := expandN 0 (level0 8 rows)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gf : allGoalFree 0 (level0 8 rows) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa0 : chunkB SA 2 ((parents.drop 0).take 1) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem paend : ((parents.drop 1)).isEmpty = true := by
  decide +kernel

theorem windowsA : windowsG (chunkB SA 2) parents 0 [1] = true :=
  windowsG_cons pa0 (windowsG_nil paend)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 531) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 531).take 535) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1066).take 126) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1192)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [531, 535, 126] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 120).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 120).take 117).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 237).take 19).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [120, 117, 19] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_nil pcend)))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 8) (nb2 := 256) (by norm_num) gf windowsC windowsB windowsA

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem witness_ok : ∀ x : Fin 6 → Bool, Circuit.eval witness (List.ofFn x) = target x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sample_ok : ∀ k : Fin 256, target (fun i => (rows.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by
  decide +kernel

theorem solve (s : ℕ) (hs : HasCircuitSize 6 target s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
  obtain ⟨C, fits, size, computes⟩ := hs
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : binaryCost C.gates < C.size :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨g, mem, by simp [isBinary, op]⟩
    have bound := bound_from_search rows rfl (by decide) reject sample_ok C.gates C.output fits computes
    refine ⟨witness, by simp [Monotone2, witness], ?_, witness_ok⟩
    change 10 ≤ s
    omega
  · refine ⟨C, ?_, size, computes⟩
    intro g mem
    obtain ⟨op, cap⟩ := fits g mem
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun eq => (hasNot ⟨g, mem, eq⟩).elim)), cap⟩

end PEqualNP.Outside.L_meta_43448

theorem PEqualNP.Outside.L_meta_43448 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4240500864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 4240500864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_43448.solve