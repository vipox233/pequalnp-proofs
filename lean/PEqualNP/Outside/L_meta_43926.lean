import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_43926

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
  Nat.testBit (4276813000 * 2 ^ 32 + 4276791424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x044b110c021536d1#64 ++ 0x00112c44300854db#64 ++ 0x0cfb111c063ffffe#64 ++ 0xbc33ec447018ffff#64 : BitVec 256),
   (0x1124067618cc8b6a#64 ++ 0x04449019d863322d#64 ++ 0x33241ffe39cc8ffd#64 ++ 0xcccc907ff8e7323f#64 : BitVec 256),
   (0x42c561a2c170d18c#64 ++ 0x110b15868b05c346#64 ++ 0xc3c7e1e3c1f0f1fb#64 ++ 0xf70f1f878f07c3c7#64 : BitVec 256),
   (0xac06ba036e00ec30#64 ++ 0x0ab01ae80db803b0#64 ++ 0xfc07fe03fe00fe37#64 ++ 0xfbf01ff80ff803f8#64 : BitVec 256),
   (0xfbb00001b5aa0000#64 ++ 0x03eec00006d6a800#64 ++ 0xfff80003ffff002f#64 ++ 0x9fffe0000ffffc00#64 : BitVec 256),
   (0xfffbddd800000000#64 ++ 0x23ffef7760000000#64 ++ 0xfffffffc0000001f#64 ++ 0xe3fffffff0000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [2, 3]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [9, 5]⟩, ⟨.and, [7, 8]⟩, ⟨.or, [0, 11]⟩, ⟨.and, [7, 10]⟩, ⟨.or, [13, 4]⟩, ⟨.and, [12, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000000000000000 0x0000000000000000 0x0cf80000063f002e 0x9c33e0000018fc00

def z1 : W := mkw 0x044b110c021536d1 0x00112c44300854db 0x0cfb111c063ffffe 0xbc33ec447018ffff

def z2 : W := mkw 0x1124067618cc8b6a 0x04449019d863322d 0x33241ffe39cc8ffd 0xcccc907ff8e7323f

def z3 : W := mkw 0x42c561a2c170d18c 0x110b15868b05c346 0xc3c7e1e3c1f0f1fb 0xf70f1f878f07c3c7

def z4 : W := mkw 0xac06ba036e00ec30 0x0ab01ae80db803b0 0xfc07fe03fe00fe37 0xfbf01ff80ff803f8

def z5 : W := mkw 0xfbb00001b5aa0000 0x03eec00006d6a800 0xfff80003ffff002f 0x9fffe0000ffffc00

def z6 : W := mkw 0xfffbddd800000000 0x23ffef7760000000 0xfffffffc063f003f 0xfffffffff018fc00

def z7 : W := mkw 0x044bdddc021536d1 0x20112f77700854db 0x0007fffc0000ffd0 0x60001ffff00003ff

def z8 : W := mkw 0xfffbddd800000000 0x23ffef7760000000 0xfffffffc0000001f 0xe3fffffff0000000

def z9 : W := mkw 0xeedbd98800000000 0x23bb6f6620000000 0xccdbe00000000002 0x23336f8000000000

def z10 : W := mkw 0xfffbddd9b5aa0000 0x23ffef7766d6a800 0xffffffffffff003f 0xfffffffffffffc00

def z11 : W := mkw 0xfffbddf88170118c 0x33ffef77e205c046 0xfffffffc01f001df 0xe7fffffff007c007

def z12 : W := mkw 0x044f312ec375f7dd 0x10113cc4bb0dd7df 0x0cfb111fc7fffffe 0xbc33ec447f1fffff

def z13 : W := mkw 0x42842022c170d18c 0x110a10808b05c346 0xc3c00003c1f0f1eb 0x970f00000f07c3c7

def z14 : W := mkw 0xfffbddd810880000 0x23ffef7760422000 0xfffffffe39cc003f 0xeffffffff8e73000

def z15 : W := mkw 0xac47fba36e50fdbc 0x1ab11fee8db943f6 0xfc07ffe3fe00fff7 0xfbf01fff8ff803ff

def z16 : W := mkw 0x044b110800101080 0x00112c4420004042 0x0cfb111c0030f1fe 0xb433ec447000c3c7

def z17 : W := mkw 0xeedbd989a5220000 0x23bb6f6626948800 0xccdbe001c6330002 0x33336f800718cc00

def z18 : W := mkw 0x044bddd800000000 0x20112f7760000000 0x0007fffc00000010 0x60001ffff0000000

def z19 : W := mkw 0x156f177e1addbffb 0x0455bc5df86b76ff 0x3fff1ffe3fffffff 0xfcfffc7ff8ffffff

def z20 : W := mkw 0x42c561a2c170d18c 0x110b15868b05c346 0xcfffe1e3c7fff1ff 0xff3fff878f1fffc7

def z21 : W := mkw 0x0000000081200000 0x0000000002048000 0x00000003c1f00020 0x140000000f07c000

def z22 : W := mkw 0x044b110802113491 0x00112c44200844d2 0x0cdb000006337002 0x30336c000018cdc0

def z23 : W := mkw 0xfbb00001b5aa0000 0x03eec00006d6a800 0xf3000003f9c00001 0x03cc00000fe70000

def z24 : W := mkw 0x044b110c021536d1 0x00112c44300854db 0x0003111c0000ffd0 0x20000c44700003ff

def z25 : W := mkw 0xfffffdda4000c000 0x23fffff769000300 0xffffffffc000f03f 0xf3ffffffff0003c0

def z26 : W := mkw 0xeec7fba3ef70fdbc 0x1bbb1fee8fbdc3f6 0xffc7ffe3fff0ffff 0xffff1fff8fffc3ff

def z27 : W := mkw 0x152616761accaf7a 0x04549859d86b32bd 0x3f271ffe3fccffff 0xfcfc9c7ff8ff33ff

def z28 : W := mkw 0xfbb00001b5aa0000 0x03eec00006d6a800 0xf3f80003f9ff0009 0x07cfe0000fe7fc00

def z29 : W := mkw 0x000420024000c000 0x0000108009000300 0xc007e003c000f033 0xf3001f800f0003c0

def z30 : W := mkw 0x044f330f6e15fef1 0x08113ccc3db857fb 0x0cfb111ffe3ffffe 0xbc33ec447ff8ffff

def z31 : W := mkw 0xffffdfffbdee8b6a 0x27ffff7ffef7ba2d 0xffffffffffff8fff 0xfffffffffffffe3f

def z32 : W := mkw 0x1120000010880000 0x0044800000422000 0x3320000239cc002d 0x8ccc800008e73000

def z33 : W := mkw 0xea900001b5aa0000 0x03aa400006d6a800 0xccd80003ffff0022 0x1f3360000ffffc00

def z34 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z35 : W := mkw 0x044b110db7bf36d1 0x00112c4436defcdb 0x0cfb111ffffffffe 0xbc33ec447fffffff

def z36 : W := mkw 0x53b0000091aa0000 0x014ec0000246a800 0x0300000001c00000 0x000c000000070000

def z37 : W := mkw 0x00000001b5aa0000 0x0000000006d6a800 0x00000003ffff0020 0x1c0000000ffffc00

def z38 : W := mkw 0xffffdfda08008820 0x23ffff7f68200220 0xfffffffe38008e3f 0xebfffffff8e00238

def z39 : W := mkw 0xeec7f9a2c170d18c 0x13bb1fe68b05c346 0xffc7ffe3c1f0f1ff 0xf7ff1fff8f07c3c7

def z40 : W := mkw 0xffffffdb6e00ec30 0x2bffffff6db803b0 0xfffffffffe00fe3f 0xfbfffffffff803f8

def z41 : W := mkw 0xac02980124000000 0x02b00a6004900000 0xfc07fe03fe000037 0xfbf01ff80ff80000

def z42 : W := mkw 0x0049010c001512c1 0x000124043000544b 0x0000011c000001c0 0x0000000470000007

def z43 : W := mkw 0x00410104001412c0 0x000104041000504b 0x00e3111c003cfffe 0xbc038c447000f3ff

def z44 : W := mkw 0x53e567f6d9fcdbee 0x154f959fdb67f36f 0xf3e7fffff9fcffff 0xffcf9fffffe7f3ff

def z45 : W := mkw 0x00042226d9fcdbee 0x140010889b67f36f 0x00000003f9fcffe0 0x1c0000000fe7f3ff

def z46 : W := mkw 0x42c1418081301084 0x110b05060204c042 0x00c0000000300000 0x000300000000c000

def z47 : W := mkw 0x0008000c00050241 0x0000200030001409 0x0038001c000f0000 0x0000e00070003c00

def z48 : W := mkw 0x53f945dc001512c1 0x214fe5177000544b 0x03f801fc003f01c8 0x040fe007f000fc07

def z49 : W := mkw 0xb9300001348a0000 0x02e4c00004d22800 0x3c3800003e0f0004 0x08f0e00000f83c00

def z50 : W := mkw 0x42c1418000000000 0x010b050600000000 0xc3c7e1e00000001b 0xe30f1f8780000000

def z51 : W := mkw 0xfffffdfac170d18c 0x33fffff7eb05c346 0xffffffffc1f0f1ff 0xf7ffffffff07c3c7

def z52 : W := mkw 0xa800000124000000 0x02a0000004900000 0xfc000003fe000027 0x9bf000000ff80000

def z53 : W := mkw 0xffb6ba03ffaaec30 0x0bfedae80ffeabb0 0xfffffe03fffffe3f 0xfffffff80ffffff8

def z54 : W := mkw 0x004561a2c170d18c 0x100115868b05c346 0x0007e1e3c1f0f1f0 0x74001f878f07c3c7

def z55 : W := mkw 0xffff177fbfffbffb 0x07fffc5dfefffeff 0xffff1fffffffffff 0xfffffc7fffffffff

def z56 : W := mkw 0xfbb0ccd000000000 0x23eec33340000000 0xf324fffc0000001d 0xc3cc93fff0000000

def z57 : W := mkw 0xb9300001348a0000 0x02e4c00004d22800 0x3cf800003e3f002e 0x9cf3e00000f8fc00

def z58 : W := mkw 0x42d9418800000000 0x210b650620000000 0x00d8000000000000 0x0003600000000000

def z59 : W := mkw 0xfbf1418000000000 0x03efc50600000000 0xffffe1e00000001f 0xe3ffff8780000000

def z60 : W := mkw 0xfbb00001a5220000 0x03eec00006948800 0xfff80001c633000f 0x93ffe0000718cc00

def z61 : W := mkw 0x00042022c170d18c 0x100010808b05c346 0x030401e3c1f0f1f9 0xd40c10078f07c3c7

def z62 : W := mkw 0x42800001b5aa0000 0x010a000006d6a800 0xc3c00003ffff002b 0x9f0f00000ffffc00

def z63 : W := mkw 0xffffffdbffaaec30 0x2bffffff6ffeabb0 0xfffffffffffffe3f 0xfffffffffffffff8

def z64 : W := mkw 0x57fb110c93bf36d1 0x015fec44324efcdb 0x0ffb111c07fffffe 0xbc3fec44701fffff

def z65 : W := mkw 0x00000001b5aa0000 0x0000000006d6a800 0x0cf80003ffff002e 0x9c33e0000ffffc00

def z66 : W := mkw 0x42c141a08170118c 0x110b05068205c046 0x03c001e001f001c8 0x040f00078007c007

def z67 : W := mkw 0xac029a012e002c30 0x0ab00a6804b800b0 0x3c001e003e000e04 0x08f0007800f80038

def z68 : W := mkw 0x004561a24050d18c 0x1001158689014346 0x0007e1e00000f1d0 0x60001f87800003c7

def z69 : W := mkw 0xac02980000000000 0x02b00a6000000000 0xfc07fe0000000017 0xe3f01ff800000000

def z70 : W := mkw 0xfbb40673bdea892a 0x07eed019cef7aa24 0xfffc0ee3ffff002f 0xdffff03b8ffffc00

def z71 : W := mkw 0x0004002200408108 0x0000100088010204 0x030401e201c081f9 0xc40c100788070207

def z72 : W := mkw 0x0049010c001512c1 0x000124043000544b 0x00f8111c003f8ffc 0x8c03e0447000fe3f

def z73 : W := mkw 0xfbf141a1b5fa118c 0x13efc50686d7e846 0xfff801e3ffff01ef 0x9fffe0078ffffc07

def z74 : W := mkw 0xbd7b9d5c021536d1 0x22f5ee75700854db 0x3cfb1f1c063ffffe 0xbcf3ec7c7018ffff

def z75 : W := mkw 0xfbf10101b5ba1080 0x03efc40406d6e842 0xfffb0103fffff1ff 0xbfffec040fffffc7

def z76 : W := mkw 0x1124067218c8892a 0x04449019c8632224 0x33040fe239c081f9 0xc4cc103f88e70207

def z77 : W := mkw 0x4284002281608108 0x010a10008a058204 0xc3c401e3c1f081fb 0xd70f10078f07c207

def z78 : W := mkw 0x53fd65fac170d18c 0x314ff597eb05c346 0xc3ffe1ffc1f0f1fb 0xf70fff87ff07c3c7

def z79 : W := mkw 0x1124067608448b6a 0x04449019d821122d 0x33241ffc00008fdd 0xc0cc907ff000023f

def z80 : W := mkw 0xa8008a012c000820 0x0aa0022804b00020 0x30000e0038000000 0x00c0003800e00000

def z81 : W := mkw 0x11240656188c8a62 0x0444901958623229 0x30241e1e380c8e35 0xc8c0907878e03238

def z82 : W := mkw 0x53e547f618cc8b6a 0x054f951fd863322d 0xf3e7fffe39cc8fff 0xefcf9ffff8e7323f

def z83 : W := mkw 0xa800a80164004000 0x0aa002a005900100 0xc000e001c0000000 0x0300038007000000

def z84 : W := mkw 0x044b110800000000 0x00112c4420000000 0x0003111c00000010 0x20000c4470000000

def z85 : W := mkw 0x1120045000000000 0x0044801140000000 0x33241ffc0000001d 0xc0cc907ff0000000

def z86 : W := mkw 0xfbb0ccd000000000 0x23eec33340000000 0xf304eee000000001 0x43cc13bb80000000

def z87 : W := mkw 0x1120047410cc034a 0x04448011d043300d 0x032001fc01cc01c8 0x040c8007f0073007

def z88 : W := mkw 0xa80420036400c000 0x02a010800d900300 0xfc07e003fe00f037 0xfbf01f800ff803c0

def z89 : W := mkw 0x00042203ffaaec30 0x080010880ffeabb0 0x00000003fffffe20 0x1c0000000ffffff8

def z90 : W := mkw 0x0402980000000000 0x00100a6000000000 0x0007fe0000000010 0x60001ff800000000

def z91 : W := mkw 0xa80422036e00ec30 0x0aa010880db803b0 0xfc000003fe00fe27 0x9bf000000ff803f8

def z92 : W := mkw 0xac06ba036e00ec30 0x0ab01ae80db803b0 0xfcfffe03fe3ffe3f 0xfff3fff80ff8fff8

def z93 : W := mkw 0xead16181e5325084 0x13ab45860794c942 0xccdbe001c6337002 0x33336f800718cdc0

def z94 : W := mkw 0x0000000400040240 0x0000000010001009 0x0020111c000c8ffc 0x8c0080447000323f

def z95 : W := mkw 0x1124067618cc8b6a 0x04449019d863322d 0x33240ffe39cc01c9 0x44cc903ff8e73007

def z96 : W := mkw 0x0000000000000000 0x0000000000000000 0x0cf800000000000e 0x8033e00000000000

def z97 : W := mkw 0x1124067218c8892a 0x04449019c8632224 0x33241ffe39c0001d 0xc0cc907ff8e70000

def z98 : W := mkw 0xfbb00451b5aa0000 0x03eec01146d6a800 0xfffc1fffffff003f 0xdffff07ffffffc00

def z99 : W := mkw 0x1124067218c8892a 0x04449019c8632224 0x33040ee239c00001 0x40cc103b88e70000

def z100 : W := mkw 0xee86faa3ef60ed3c 0x1bba1bea8fbd83b4 0xff07fee3ffc0fe37 0xfbfc1ffb8fff03f8

def z101 : W := mkw 0x0000065408040a62 0x0400001950201029 0x00001e1c00000e00 0x0000007870000038

def z102 : W := mkw 0x000420224040c108 0x0000108089010304 0xc307e1e3c1c0f1fb 0xf70c1f878f0703c7

def z103 : W := mkw 0x0004022618cc8b6a 0x040010089863322d 0x0000000239cc8fe0 0x0c00000008e7323f

def z104 : W := mkw 0x1124047610cc834a 0x04449011d843320d 0x032401fe01cc81f9 0xc40c9007f8073207

def z105 : W := mkw 0xbd7bddd800000000 0x22f5ef7760000000 0x3c3ffffc00000014 0x60f0fffff0000000

def z106 : W := mkw 0x53b0000091aa0000 0x014ec0000246a800 0x03f8000001ff0008 0x040fe0000007fc00

def z107 : W := mkw 0xfbb4cef618cc8b6a 0x27eed33bd863322d 0xf324fffe39cc8ffd 0xcfcc93fff8e7323f

def z108 : W := mkw 0x1124067618cc8b6a 0x04449019d863322d 0x30241ffc380c8fd4 0x48c0907ff0e0323f

def z109 : W := mkw 0x0406ba024a00ec30 0x08101ae8092803b0 0xc007fe03c000fe33 0xf3001ff80f0003f8

def z110 : W := mkw 0x0402100002002410 0x0010084000080090 0x0c0310000600fe36 0xb8300c40001803f8

def z111 : W := mkw 0xac4fbb0f6e15fef1 0x0ab13eec3db857fb 0xfcffff1ffe3fffff 0xfff3fffc7ff8ffff

def z112 : W := mkw 0xffb6ba03ffaaec30 0x0bfedae80ffeabb0 0xff07fe03ffc0fe37 0xfbfc1ff80fff03f8

def z113 : W := mkw 0xac02ba016e006c30 0x0ab00ae805b801b0 0xfc03fe01fe007e06 0x3bf00ff807f801f8

def z114 : W := mkw 0xac06b8036600e410 0x0ab01ae00d980390 0xcc07e003c600f033 0xf3301f800f1803c0

def z115 : W := mkw 0x00042022c170d18c 0x100010808b05c346 0x00000003c1f0f1e0 0x140000000f07c3c7

def z116 : W := mkw 0xac06ba024a00ec30 0x0ab01ae8092803b0 0xfc07fe000000fe17 0xe3f01ff8000003f8

def z117 : W := mkw 0xbd26be777eccef7a 0x0ef49af9ddfb33bd 0xff27ffffffccffff 0xfffc9fffffff33ff

def z118 : W := mkw 0x0004067608448b6a 0x04001019d821122d 0x00041ffc00008fd0 0x4000107ff000023f

def z119 : W := mkw 0xfffffffbef70fdbc 0x3bffffffefbdc3f6 0xfffffffffff0ffff 0xffffffffffffc3ff

def z120 : W := mkw 0x53b00001b5aa0000 0x014ec00006d6a800 0x03f80003ffff0028 0x1c0fe0000ffffc00

def z121 : W := mkw 0x1124067618cc8b6a 0x04449019d863322d 0x3ffc1ffe3fff8fff 0xdcfff07ff8fffe3f

def z122 : W := mkw 0xfffffffed9fcdbee 0x37fffffffb67f36f 0xfffffffff9fcffff 0xffffffffffe7f3ff

def z123 : W := mkw 0xac02b80166006410 0x0ab00ae005980190 0xcc03e001c6007002 0x33300f80071801c0

def z124 : W := mkw 0x1526be765accef7a 0x0c549af9d96b33bd 0x3327fffe39ccfffd 0xeccc9ffff8e733ff

def z125 : W := mkw 0x000422024a00ec30 0x08001088092803b0 0x000000000000fe00 0x00000000000003f8

def z126 : W := mkw 0xeedbd98802113491 0x23bb6f66200844d2 0xccdbe00006337002 0x33336f800018cdc0

def z127 : W := mkw 0xfbb0ccd1b5aa0000 0x23eec33346d6a800 0xfffceee3ffff002f 0xdffff3bb8ffffc00

def z128 : W := mkw 0x000422024800c820 0x0000108809200320 0xf007fe03f800fe37 0xfbc01ff80fe003f8

def z129 : W := mkw 0x044b110c021536d1 0x00112c44300854db 0x0cdb111c0633ffd2 0x30336c447018cfff

def z130 : W := mkw 0x53e547f699fc9bee 0x154f951fda67f26f 0x33e41ffe39fc8ffd 0xcccf907ff8e7f23f

def z131 : W := mkw 0xffb29a01bfaa2c30 0x0bfeca6806fea8b0 0xfff81e03ffff0e2f 0x9fffe0780ffffc38

def z132 : W := mkw 0x0406ba024a00ec30 0x08101ae8092803b0 0x0007fe000000fe10 0x60001ff8000003f8

def z133 : W := mkw 0x044b110802113491 0x00112c44200844d2 0x0003000000007000 0x20000c00000001c0

def z134 : W := mkw 0xfbf5edf2c170d18c 0x33efd7b7cb05c346 0xf3c7efe3c1f0f1fb 0xf7cf1fbf8f07c3c7

def z135 : W := mkw 0x004567f64854dbee 0x1401159fd921536f 0x0007fffc0000ffd0 0x60001ffff00003ff

def z136 : W := mkw 0x4280000081200000 0x010a000002048000 0xc3c00003c1f0002b 0x970f00000f07c000

def z137 : W := mkw 0x116567f658dcdbee 0x1445959fd963736f 0x3327fffe39ccfffd 0xeccc9ffff8e733ff

def z138 : W := mkw 0xfffbddd924000000 0x23ffef7764900000 0xfffffffffe00003f 0xfbfffffffff80000

def z139 : W := mkw 0x000420024000c000 0x0000108009000300 0xc004e003c0000001 0x430013800f000000

def z140 : W := mkw 0xfbb0000091aa0000 0x03eec0000246a800 0xfff8000001ff000f 0x87ffe0000007fc00

def z141 : W := mkw 0x000422036e00ec30 0x080010880db803b0 0x00000003fe00fe20 0x180000000ff803f8

def z142 : W := mkw 0xea800001a5200000 0x03aa000006948000 0xffc00003fff0002f 0x9fff00000fffc000

def z143 : W := mkw 0x53f945d800000000 0x214fe51760000000 0x03f801fc00000008 0x000fe007f0000000

def z144 : W := mkw 0x0402100000000000 0x0010084000000000 0x0c03100000000016 0xa0300c4000000000

def z145 : W := mkw 0x00000005b7bf36d1 0x0000000016defcdb 0x00000003ffffffe0 0x1c0000000fffffff

def z146 : W := mkw 0x11200654188c0a62 0x0444801950623029 0x30201e1c380c0e04 0x08c0807870e03038

def z147 : W := mkw 0x42c16180c1305084 0x110b05860304c142 0xc0c3e001c0307002 0x33030f800700c1c0

def z148 : W := mkw 0x46c7fba2cb70fdbc 0x191b1fee8b2dc3f6 0xc3c7ffe3c1f0fffb 0xf70f1fff8f07c3ff

def z149 : W := mkw 0xac4bddd800000000 0x22b12f7760000000 0xfc07fffc00000017 0xe3f01ffff0000000

def z150 : W := mkw 0x53fd47fe18cc8b6a 0x254ff51ff863322d 0x33fc1ffe39cc8ffd 0xcccff07ff8e7323f

def z151 : W := mkw 0xfbb4aa03fdaac820 0x0beed2a80ff6ab20 0xfffcee03ffff002f 0xdffff3b80ffffc00

def z152 : W := mkw 0x1120067418cc0b6a 0x04448019d063302d 0x33201ffc39cc0fcc 0x0ccc807ff0e7303f

def z153 : W := mkw 0xac029a012e002c30 0x0ab00a6804b800b0 0xfc07fe003e000e17 0xebf01ff800f80038

def z154 : W := mkw 0xfffffdfbf5fad18c 0x33fffff7efd7eb46 0xfffffffffffff1ff 0xffffffffffffffc7

def z155 : W := mkw 0x156b175c1a9d3ef3 0x0455ac5d706a74fb 0x3cfb1f1c3e3ffffe 0xbcf3ec7c70f8ffff

def z156 : W := mkw 0x0041010000101080 0x0001040400004042 0x0cfb0100063ff1fe 0xbc33ec040018ffc7

def z157 : W := mkw 0xfbf14181b5aa0000 0x03efc50606d6a800 0xffffe1e3ffff003f 0xffffff878ffffc00

def z158 : W := mkw 0x428460a2c160c10c 0x110a11828b058304 0xc3c4e0e3c1f0002b 0xd70f13838f07c000

def z159 : W := mkw 0xffffdffe18cc8b6a 0x27ffff7ff863322d 0xfffffffe39cc8fff 0xeffffffff8e7323f

def z160 : W := mkw 0xbd7b110d369f36d1 0x02f5ec4434da7cdb 0x3cfb111c3e3ffffe 0xbcf3ec4470f8ffff

def z161 : W := mkw 0xbd329a013e8a2c30 0x0af4ca6804fa28b0 0x3c381e003e0f0e04 0x08f0e07800f83c38

def z162 : W := mkw 0x044fbb0e4a15fef1 0x08113eec392857fb 0x0cffff1c063ffffe 0xfc33fffc7018ffff

def z163 : W := mkw 0x42c561a2c170d18c 0x110b15868b05c346 0xc0c3e003c1f0f1e2 0x37030f800f07c3c7

def z164 : W := mkw 0x11200001b5aa0000 0x0044800006d6a800 0x33200003ffff002d 0x9ccc80000ffffc00

def z165 : W := mkw 0x0004022608448b6a 0x040010089821122d 0x0000000000008fc0 0x000000000000023f

def z166 : W := mkw 0x00000004021536d1 0x00000000100854db 0x00000000063fffe0 0x1c0000000018ffff

def z167 : W := mkw 0x0004020208008820 0x0000100808200220 0x30041e0238008e35 0xc8c0107808e00238

def z168 : W := mkw 0x42c161a0c170518c 0x110b05868305c146 0xc3c3e1e1c1f071ca 0x370f0f878707c1c7

def z169 : W := mkw 0x11300000108a0000 0x0044c00000422800 0x00380000000f0000 0x0000e00000003c00

def z170 : W := mkw 0xbd3a9c59348a0000 0x22f4ea7164d22800 0x3c381e1c3e0f0004 0x08f0e07870f83c00

def z171 : W := mkw 0x040a100c02052651 0x0010284030081499 0x0c38101c060f0e04 0x0830e04070183c38

def z172 : W := mkw 0x428460a2c160c10c 0x110a11828b058304 0xc304e0e3c1c00001 0x430c13838f070000

def z173 : W := mkw 0xeac5eba3ed70d9ac 0x1bab17ae8fb5c366 0xf3c7efe3f9f0f1fb 0xf7cf1fbf8fe7c3c7

def z174 : W := mkw 0xa800000124000000 0x02a0000004900000 0xf0000003f8000001 0x03c000000fe00000

def z175 : W := mkw 0xbd3a9c5800000000 0x22f4ea7160000000 0x3c381e1c00000004 0x00f0e07870000000

def z176 : W := mkw 0x1124065208008820 0x0044901948200220 0x33241ffe38008e3d 0xc8cc907ff8e00238

def z177 : W := mkw 0xeedbf98966006410 0x2bbb6fe625980190 0xccdbe001c6007002 0x33336f80071801c0

def z178 : W := mkw 0x53a466f6d9eccb6e 0x154e919bdb67b32d 0xf324fffff9cc8ffd 0xcfcc93ffffe7323f

def z179 : W := mkw 0x00000004021536d1 0x00000000100854db 0x000000000000ffc0 0x00000000000003ff

def z180 : W := mkw 0x0004067608448b6a 0x04001019d821122d 0x03041ffe01c08ff9 0xc40c107ff807023f

def z181 : W := mkw 0xfffb1109b7bb3491 0x03ffec4426deecd2 0xfffb0003ffff702f 0xbfffec000ffffdc0

def z182 : W := mkw 0x0041010000101080 0x0001040400004042 0x00c301000030f1fa 0xb4030c040000c3c7

def z183 : W := mkw 0xfffbddd800101080 0x23ffef7760004042 0xfffffffc0030f1ff 0xf7fffffff000c3c7

def z184 : W := mkw 0x0000000000000000 0x0000000000000000 0x00f80000003f0008 0x0403e0000000fc00

def z185 : W := mkw 0x42c561a2c170d18c 0x110b15868b05c346 0xc307e1e3c1c0f1d1 0x630c1f878f0703c7

def z186 : W := mkw 0x42c141a08170118c 0x110b05068205c046 0xc3c7e1e001f001db 0xe70f1f878007c007

def z187 : W := mkw 0x00042026c375f7dd 0x100010809b0dd7df 0x00000003c7ffffe0 0x1c0000000f1fffff

def z188 : W := mkw 0xfbf9010db5bf12c1 0x03efe40436d6fc4b 0xfff8011fffff01ef 0x9fffe0047ffffc07

def z189 : W := mkw 0x00000004001512c1 0x000000001000544b 0x00000000003f01c0 0x040000000000fc07

def z190 : W := mkw 0xea900001a5220000 0x03aa400006948800 0xcfd80003c7f3002b 0x973f60000f1fcc00

def z191 : W := mkw 0xac06be776e44ef7a 0x0eb01af9ddb913bd 0xfc07fffffe00fff7 0xfbf01ffffff803ff

def z192 : W := mkw 0xfbf561a3f5fad18c 0x13efd5868fd7eb46 0xffffe1e3fffff1ff 0xffffff878fffffc7

def z193 : W := mkw 0x000420224050d18c 0x1000108089014346 0x000000000000f1c0 0x00000000000003c7

def z194 : W := mkw 0x42c561a2c170d18c 0x110b15868b05c346 0x03c001e3c1f0f1e8 0x140f00078f07c3c7

def z195 : W := mkw 0x044b110800000000 0x00112c4420000000 0x0cfb111c063f003e 0xbc33ec447018fc00

def z196 : W := mkw 0xeedbddd800000000 0x23bb6f7760000000 0xccdffffc00000012 0x63337ffff0000000

def z197 : W := mkw 0x044b110c021536d1 0x00112c44300854db 0x0cdb0000063fffe2 0x3c336c000018ffff

def z198 : W := mkw 0x044b110800000000 0x00112c4420000000 0x0cfb111c0000001e 0xa033ec4470000000

def z199 : W := mkw 0x156b110c129d36d1 0x0055ac44304a74db 0x3ffb111e3fffffff 0xbcffec4478ffffff

def z200 : W := mkw 0xfbf16181f5ba5084 0x13efc58607d6e942 0xfffbe003ffff702f 0xbfffef800ffffdc0

def z201 : W := mkw 0xfbb40677bdee8b6a 0x07eed019def7ba2d 0xfffc1fffffff8fff 0xdffff07ffffffe3f

def z202 : W := mkw 0x000406720840892a 0x04001019c8210224 0x00040ee000000000 0x4000103b80000000

def z203 : W := mkw 0x0402100002002410 0x0010084000080090 0x000310000000fe10 0x20000c40000003f8

def z204 : W := mkw 0xfffbdddc021536d1 0x23ffef77700854db 0xfffffffc063fffff 0xfffffffff018ffff

def z205 : W := mkw 0xa810000124020000 0x02a0400004900800 0x0c18000006030000 0x0030600000180c00

def z206 : W := mkw 0x044b110c021536d1 0x00112c44300854db 0x0cfb011c063f71ca 0x3433ec047018fdc7

def z207 : W := mkw 0x0000ccd000000000 0x2000033340000000 0x0004eee000000000 0x400013bb80000000

def z208 : W := mkw 0xead561a3e572d18c 0x13ab55868f95cb46 0xcfdfe1e3c7f3f1fb 0xf73f7f878f1fcfc7

def z209 : W := mkw 0x0000000400040240 0x0000000010001009 0x0020011c000c01c8 0x0400800470003007

def z210 : W := mkw 0x040a100800000000 0x0010284020000000 0x0c38101c00000004 0x0030e04070000000

def z211 : W := mkw 0x53f945d800000000 0x214fe51760000000 0xc3ffe1fc0000001b 0xe30fff87f0000000

def z212 : W := mkw 0xac06ba076e04ee70 0x0ab01ae81db813b9 0xfc27ff1ffe0cffff 0xfff09ffc7ff833ff

def z213 : W := mkw 0x42c1418081200000 0x010b050602048000 0xc3c7e1e3c1f0003b 0xf70f1f878f07c000

def z214 : W := mkw 0xea90c88000000000 0x23aa432200000000 0xc000e00000000000 0x0300038000000000

def z215 : W := mkw 0xfffb110db7bf36d1 0x03ffec4436defcdb 0xfffb111fffffffff 0xbfffec447fffffff

def z216 : W := mkw 0xac06ba236e40ed38 0x0ab01ae88db903b4 0xff07ffe3ffc0ffff 0xfffc1fff8fff03ff

def z217 : W := mkw 0xfffbd98800000000 0x23ffef6620000000 0xfffbe0000000000f 0xa3ffef8000000000

def z218 : W := mkw 0x0000000002113491 0x00000000000844d2 0x0000000006337000 0x100000000018cdc0

def z219 : W := mkw 0x044b110c021536d1 0x00112c44300854db 0x0cfb101c063f7e06 0x3833ec407018fdf8

def z220 : W := mkw 0x0004002200408108 0x0000100088010204 0x000401e0000081d0 0x4000100780000207

def z221 : W := mkw 0x0000000400040240 0x0000000010001009 0x0020101c000c0e04 0x0800804070003038

def z222 : W := mkw 0x0004020208008820 0x0000100808200220 0x30040e0238000001 0x40c0103808e00000

def z223 : W := mkw 0x4290000081220000 0x010a400002048800 0x00d8000000330000 0x000360000000cc00

def z224 : W := mkw 0x1124022618cc8b6a 0x044490089863322d 0x3320000239cc8fed 0x8ccc800008e7323f

def z225 : W := mkw 0xb924ae737cc8c92a 0x0ee492b9cdf32324 0xf304eee3f9c00001 0x43cc13bb8fe70000

def z226 : W := mkw 0x000420024000c000 0x0000108009000300 0x00000003c000f020 0x100000000f0003c0

def z227 : W := mkw 0xa804aa036e00ec30 0x0aa012a80db803b0 0xf004ee03fe00fe21 0x5bc013b80ff803f8

def z228 : W := mkw 0x000422277eccef7a 0x0c0010889dfb33bd 0x00000003ffccffe0 0x1c0000000fff33ff

def z229 : W := mkw 0xb93006553c8e0a62 0x06e4c01954f23829 0x3c381e1c3e0f0e04 0x08f0e07870f83c38

def z230 : W := mkw 0xa804aa036c00c820 0x0aa012a80db00320 0xf004ee03f8000001 0x43c013b80fe00000

def z231 : W := mkw 0xac069a032e00ac30 0x0ab01a680cb802b0 0x3c041e023e008e35 0xc8f0107808f80238

def z232 : W := mkw 0xfbb40227bdee8b6a 0x07eed0089ef7ba2d 0xfff80003ffff8fef 0x9fffe0000ffffe3f

def z233 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0000003c0000023 0x930000000f000000

def z234 : W := mkw 0xa800000124000000 0x02a0000004900000 0x3c0000003e000004 0x08f0000000f80000

def z235 : W := mkw 0x11200654188c0a62 0x0444801950623029 0x33241ffc380c0e1d 0xc8cc907ff0e03038

def z236 : W := mkw 0x044f177e0a55bffb 0x04113c5df82956ff 0x0cff1ffc063ffffe 0xfc33fc7ff018ffff

def z237 : W := mkw 0x040a100c02052651 0x0010284030081499 0x0cf8101c063f0e2e 0x9c33e0407018fc38

def z238 : W := mkw 0xac06ba036c00c820 0x0ab01ae80db00320 0xfc07fe03f8000017 0xe3f01ff80fe00000

def z239 : W := mkw 0x53e565f6d1fcd3ce 0x154f9597db47f34f 0xc3e7e1ffc1fcf1fb 0xf70f9f87ff07f3c7

def z240 : W := mkw 0x42c1418000101080 0x010b050600004042 0xc3c7e1e00030f1fb 0xf70f1f878000c3c7

def z241 : W := mkw 0x42c561a6c375f7dd 0x110b15869b0dd7df 0xc3c7e1e3c7fffffb 0xff0f1f878f1fffff

def z242 : W := mkw 0x53f9010c91bf12c1 0x014fe4043246fc4b 0x03f8011c01ff01c8 0x040fe0047007fc07

def z243 : W := mkw 0xfbb4cef218c8892a 0x27eed33bc8632224 0xf304eee239c00001 0x43cc13bb88e70000

def z244 : W := mkw 0xeedbf988c1305084 0x33bb6fe62304c142 0xccdbe001c0307002 0x33336f800700c1c0

def z245 : W := mkw 0x0041010000101080 0x0001040400004042 0x00c3000000307002 0x30030c000000c1c0

def z246 : W := mkw 0x000422076e15fef1 0x080010881db857fb 0x00000003fe3fffe0 0x1c0000000ff8ffff

def z247 : W := mkw 0x156f177e18cc8b6a 0x0455bc5df863322d 0x3fff1ffe39cc8fff 0xecfffc7ff8e7323f

def z248 : W := mkw 0xac02b80166006410 0x0ab00ae005980190 0xfc03e003fe007027 0xbbf00f800ff801c0

def z249 : W := mkw 0x004561a24050d18c 0x1001158689014346 0xc007e1e3c000f1f3 0xf3001f878f0003c7

def z250 : W := mkw 0xac1a980800000000 0x22b06a6020000000 0x0c18000000000000 0x0030600000000000

def z251 : W := mkw 0x1124267658cccb6a 0x04449099d963332d 0xf327fffff9ccffff 0xffcc9fffffe733ff

def z252 : W := mkw 0xfffffdfa4050d18c 0x33fffff7e9014346 0xfffffffc0000f1df 0xe3fffffff00003c7

def z253 : W := mkw 0x0000000091aa0000 0x000000000246a800 0x0000000001ff0000 0x040000000007fc00

def z254 : W := mkw 0x46cf71aec375f7dd 0x111b3dc6bb0dd7df 0xcffff1ffc7ffffff 0xff3fffc7ff1fffff

def z255 : W := mkw 0xfbb00001b5aa0000 0x03eec00006d6a800 0x3ff800003fff000c 0x0cffe00000fffc00

def z256 : W := mkw 0xfbb0000124000000 0x03eec00004900000 0xfff80003fe00002f 0x9bffe0000ff80000

def z257 : W := mkw 0x0004020608048a60 0x0000100818201229 0x30241f1e380c8ffd 0xccc0907c78e0323f

def z258 : W := mkw 0xfffbddd800000000 0x23ffef7760000000 0xfcfbfe1c00000006 0x23f3eff870000000

def z259 : W := mkw 0xfffbddd800000000 0x23ffef7760000000 0xffdfeee000000003 0x63ff7fbb80000000

def z260 : W := mkw 0xffffdffe1addbffb 0x27ffff7ff86b76ff 0xfffffffe3fffffff 0xfffffffff8ffffff

def z261 : W := mkw 0x42cd61aec175d3cd 0x110b3586bb05d74f 0xc3ffe1ffc1fff1fb 0xf70fff87ff07ffc7

def z262 : W := mkw 0x428460a2c160c10c 0x110a11828b058304 0xc307e0e3c1c0f033 0xf30c1f838f0703c0

def z263 : W := mkw 0xfbb0ccd000000000 0x23eec33340000000 0xfffceee00000000f 0xc3fff3bb80000000

def z264 : W := mkw 0x0004002600448348 0x000010009801120d 0x032411fe01cc8ffd 0xcc0c9047f807323f

def z265 : W := mkw 0x112406761addbffb 0x04449019d86b76ff 0x33241ffe3ffffffd 0xdccc907ff8ffffff

def z266 : W := mkw 0x53b0000091aa0000 0x014ec0000246a800 0xc3f80003c1ff002b 0x970fe0000f07fc00

def z267 : W := mkw 0x46c771a2c370f59c 0x111b1dc68b0dc3d6 0xcfc7f1e3c7f0ffff 0xff3f1fc78f1fc3ff

def z268 : W := mkw 0x0406ba024a00ec30 0x08101ae8092803b0 0x0c07fe000600fe36 0xf8301ff8001803f8

def z269 : W := mkw 0x0000000000000000 0x0000000000000000 0x30041e0000000015 0xc0c0107800000000

def z270 : W := mkw 0x1120045010880000 0x0044801140422000 0x33241ffe39cc003d 0xcccc907ff8e73000

def z271 : W := mkw 0x0000200040004000 0x0000008001000100 0xc003e001c0007002 0x33000f80070001c0

def z272 : W := mkw 0xfffbd989b5aa0000 0x23ffef6626d6a800 0xfffbe003ffff002f 0xbfffef800ffffc00

def z273 : W := mkw 0x0049010800000000 0x0001240420000000 0x00f8011c00000008 0x0003e00470000000

def z274 : W := mkw 0x1124067618cc8b6a 0x04449019d863322d 0x33041ffe39c08fd1 0x40cc107ff8e7023f

def z275 : W := mkw 0x004561a24050d18c 0x1001158689014346 0x00c7e1e00030f1fa 0xf4031f878000c3c7

def z276 : W := mkw 0xbd3a9c5800000000 0x22f4ea7160000000 0x3f3c1ffc0000001d 0xc0fcf07ff0000000

def z277 : W := mkw 0x044b110c021536d1 0x00112c44300854db 0x0cfb111c0000ffde 0xa033ec44700003ff

def z278 : W := mkw 0xffff71aff7fff7dd 0x13fffdc6bfdfffdf 0xfffff1ffffffffff 0xffffffc7ffffffff

def z279 : W := mkw 0xfffbddd800000000 0x23ffef7760000000 0xcffbe1fc0000000a 0x233fef87f0000000

def z280 : W := mkw 0xac06ba036e00ec30 0x0ab01ae80db803b0 0xcc07fe01c600fe12 0x73301ff8071803f8

def z281 : W := mkw 0x156b155800000000 0x0055ac5560000000 0x3fff1ffc0000001f 0xe0fffc7ff0000000

def z282 : W := mkw 0x0406ba024a00ec30 0x08101ae8092803b0 0x3007fe023800fe35 0xe8c01ff808e003f8

def z283 : W := mkw 0x000420024000c000 0x0000108009000300 0x0007e0000000f010 0x60001f80000003c0

def z284 : W := mkw 0xfffbddd881200000 0x23ffef7762048000 0xffffffffc1f0003f 0xf7ffffffff07c000

def z285 : W := mkw 0x0000000000000000 0x0000000000000000 0x0c380000060f0004 0x0830e00000183c00

def z286 : W := mkw 0x4280408000000000 0x010a010200000000 0xc304e0e000000001 0x430c138380000000

def z287 : W := mkw 0xea900001a5220000 0x03aa400006948800 0xccd80001c6330002 0x133360000718cc00

def z288 : W := mkw 0x46cbddd800000000 0x211b2f7760000000 0xc3c7fffc0000001b 0xe30f1ffff0000000

def z289 : W := mkw 0x044b110c001512c1 0x00112c443000544b 0x0cfb111c003f01de 0xa433ec447000fc07

def z290 : W := mkw 0x0045012200509188 0x0001140488014246 0x03c701e201f0f1fb 0xf40f1c078807c3c7

def z291 : W := mkw 0xac06ba036e00ec30 0x0ab01ae80db803b0 0xf007fe03f800fe11 0x63c01ff80fe003f8

def z292 : W := mkw 0xfbb0000000000000 0x03eec00000000000 0xfff800000000000f 0x83ffe00000000000

def z293 : W := mkw 0x46cb110c833536d1 0x011b2c44320cd4db 0xcffb111fc7ffffff 0xbf3fec447f1fffff

def z294 : W := mkw 0xac4fbb0b6e11fcb1 0x0ab13eec2db847f2 0xfcdffe03fe33fe37 0xfbf37ff80ff8cff8

def z295 : W := mkw 0xbd229c5000000000 0x02f48a7140000000 0xff27fffc0000001f 0xe3fc9ffff0000000

def z296 : W := mkw 0xffb29801b5aa0000 0x03feca6006d6a800 0xfffffe03ffff003f 0xfffffff80ffffc00

def z297 : W := mkw 0xfbb00001b5aa0000 0x03eec00006d6a800 0xff000003ffc00027 0x9bfc00000fff0000

def z298 : W := mkw 0x53a466f2d9e8c92e 0x154e919bcb67a324 0xf304eee3f9c00001 0x43cc13bb8fe70000

def z299 : W := mkw 0x53a0000091a80000 0x014e80000246a000 0xf3e00003f9fc002f 0x9fcf80000fe7f000

def z300 : W := mkw 0xfbb0000010880000 0x03eec00000422000 0xfff8000239cc002f 0x8fffe00008e73000

def z301 : W := mkw 0xffb6fed36e00ec30 0x2bfedbfb4db803b0 0xff07fee3fe00fe37 0xfbfc1ffb8ff803f8

def z302 : W := mkw 0xeedbd98800000000 0x23bb6f6620000000 0xcfdfe1e00000001b 0xe33f7f8780000000

def z303 : W := mkw 0x1120047410cc034a 0x04448011d043300d 0x032011fc01cc8ffc 0x8c0c8047f007323f

def z304 : W := mkw 0xa80402032c008820 0x02a010080cb00220 0xfc041e03fe008e37 0xdbf010780ff80238

def z305 : W := mkw 0xac06ba277eccef7a 0x0eb01ae89dfb33bd 0xfc07fe03ffccfff7 0xfff01ff80fff33ff

def z306 : W := mkw 0xb93406773cce8b6a 0x06e4d019dcf33a2d 0x3f3c1ffe3fcf8ffd 0xccfcf07ff8ff3e3f

def z307 : W := mkw 0xeecffbafef75fffd 0x1bbb3feebfbdd7ff 0xffffffffffffffff 0xffffffffffffffff

def z308 : W := mkw 0xfbb40203bdaa8820 0x03eed0080ef6aa20 0xfffc1e03ffff8e3f 0xdffff0780ffffe38

def z309 : W := mkw 0xffbadcd800000000 0x23feeb7360000000 0xff3cfefc00000005 0x43fcf3fbf0000000

def z310 : W := mkw 0xb930000000000000 0x02e4c00000000000 0x3c38000000000004 0x00f0e00000000000

def z311 : W := mkw 0x42c561824000c000 0x010b158609000300 0xc3c7e1e3c000f03b 0xf30f1f878f0003c0

def z312 : W := mkw 0xfffbddddb7bf36d1 0x23ffef7776defcdb 0xffffffffffffffff 0xffffffffffffffff

def z313 : W := mkw 0xfffbddd9b5aa0000 0x23ffef7766d6a800 0xfffffffff9c0001f 0xe3ffffffffe70000

def z314 : W := mkw 0x46cb718cc33576d5 0x111b2dc6330cd5db 0xccfbf11dc63ffffe 0xbf33efc47718ffff

def z315 : W := mkw 0x1120000010880000 0x0044800000422000 0x0320000001cc0008 0x040c800000073000

def z316 : W := mkw 0x044b110802113491 0x00112c44200844d2 0x0cfb111c0633701e 0xb033ec447018cdc0

def z317 : W := mkw 0xeedff9aac170d18c 0x33bb7fe6ab05c346 0xcfdfe1e3c1f0f1fb 0xf73f7f878f07c3c7

def z318 : W := mkw 0xfbb4ecf2c160c10c 0x33eed3b3cb058304 0xf304eee3c1c00001 0x43cc13bb8f070000

def z319 : W := mkw 0x4280000081200000 0x010a000002048000 0xc3000003c1c00001 0x030c00000f070000

def z320 : W := mkw 0xfbb00001b5aa0000 0x03eec00006d6a800 0xf3200003f9cc002d 0x8fcc80000fe73000

def z321 : W := mkw 0x53b0000091aa0000 0x014ec0000246a800 0x0ff8000007ff002e 0x9c3fe000001ffc00

def z322 : W := mkw 0x156b157c12dd37db 0x0455ac55f04b74df 0x0ffb11fc07fffffe 0xbc3fec47f01fffff

def z323 : W := mkw 0xac02980002002410 0x02b00a6000080090 0xfc07fe000600fe37 0xfbf01ff8001803f8

def z324 : W := mkw 0x000422036e00ec30 0x080010880db803b0 0x30041e03fe00fe35 0xd8c010780ff803f8

def z325 : W := mkw 0xac4bb90966117491 0x0ab12ee4259845d2 0xccdbe001c6337002 0x33336f800718cdc0

def z326 : W := mkw 0xeedb1109a7333491 0x03bb6c44269cccd2 0xccdb0001c6337002 0x33336c000718cdc0

def z327 : W := mkw 0x044b110c021536d1 0x00112c44300854db 0x00fb111c003fffd8 0x2403ec447000ffff

def z328 : W := mkw 0x0000000400040240 0x0000000010001009 0x0000111c00008fd0 0x000000447000023f

def z329 : W := mkw 0x044bddd800000000 0x20112f7760000000 0x0cfffffc0000001e 0xe033fffff0000000

def z330 : W := mkw 0xfbb0045000000000 0x03eec01140000000 0xfffc1ffc0000001f 0xc3fff07ff0000000

def z331 : W := mkw 0x044b110c021536d1 0x00112c44300854db 0x0cf8111c063f0fcc 0x0c33e0447018fc3f

def z332 : W := mkw 0xfbf9cdd800000000 0x23efe73760000000 0xf3fceffc00000009 0x43cff3bff0000000

def z333 : W := mkw 0xfffbddfc10cc034a 0x27ffef77f043300d 0xfffffffc01cc01df 0xe7fffffff0073007

def z334 : W := mkw 0x040a100c02052651 0x0010284030081499 0x0c3b101c060ffe36 0xb830ec4070183ff8

def z335 : W := mkw 0xee86ba03ef20ec30 0x0bba1ae80fbc83b0 0xffc7fe03fff0fe3f 0xffff1ff80fffc3f8

def z336 : W := mkw 0xbd3a9e5c188c0a62 0x26f4ea7970623029 0x3c381e1c380c0e04 0x08f0e07870e03038

def z337 : W := mkw 0x46cf71aac371f59d 0x111b3dc6ab0dc7d6 0xcfdfe1e3c7f3f1fb 0xf73f7f878f1fcfc7

def z338 : W := mkw 0x53e145f491fc13ce 0x154f8517d247f04f 0x03e001fc01fc01c8 0x040f8007f007f007

def z339 : W := mkw 0xeec7fb83ef30fcb4 0x1bbb1fee0fbcc3f2 0xfcc7fe03fe30fe37 0xfbf31ff80ff8c3f8

def z340 : W := mkw 0x4280000000000000 0x010a000000000000 0xc3c000000000000b 0x830f000000000000

def z341 : W := mkw 0x42c561a2c170d18c 0x110b15868b05c346 0xc3c4e1e3c1f001c9 0x470f13878f07c007

def z342 : W := mkw 0xb920000134880000 0x02e4800004d22000 0xff200003ffcc002f 0x9ffc80000fff3000

def z343 : W := mkw 0x000422036e00ec30 0x080010880db803b0 0xc007e003fe00fe33 0xfb001f800ff803f8

def z344 : W := mkw 0xfbb00005b7bf36d1 0x03eec00016defcdb 0xfff80003ffffffef 0x9fffe0000fffffff

def z345 : W := mkw 0xb9308c5000000000 0x22e4c23140000000 0x30000e0000000000 0x00c0003800000000

def z346 : W := mkw 0x0000000000000000 0x0000000000000000 0x030401e000000019 0xc00c100780000000

def z347 : W := mkw 0x53e145d000000000 0x014f851740000000 0xf3e7fffc0000001f 0xe3cf9ffff0000000

def z348 : W := mkw 0x42c541a200408108 0x010b150688010204 0xc3c7e1e201c081fb 0xe70f1f8788070207

def z349 : W := mkw 0xeac561a3e570d18c 0x13ab15868f95c346 0xffc7e1e3fff0f1ff 0xffff1f878fffc3c7

def z350 : W := mkw 0x42c567f6c974dbee 0x150b159fdb25d36f 0xc3c7ffffc1f0fffb 0xf70f1fffff07c3ff

def z351 : W := mkw 0xbd3ebe5b6e00ec30 0x2af4faf96db803b0 0xfc3ffe1ffe00fe37 0xfbf0fff87ff803f8

def z352 : W := mkw 0xfffb110c021536d1 0x03ffec44300854db 0xfffb111c063fffff 0xbfffec447018ffff

def z353 : W := mkw 0xfbb0ccd1b5aa0000 0x23eec33346d6a800 0xf304eee3f9c00001 0x43cc13bb8fe70000

def z354 : W := mkw 0x53f945fc10cc034a 0x254fe517f043300d 0x03f801fc01cc01c8 0x040fe007f0073007

def z355 : W := mkw 0xa800000000000000 0x02a0000000000000 0xfc00000000000007 0x83f0000000000000

def z356 : W := mkw 0x0041010000101080 0x0001040400004042 0x00c00100003001c8 0x040300040000c007

def z357 : W := mkw 0x044fbb0e4a15fef1 0x08113eec392857fb 0x0007ff1c0000ffd0 0x60001ffc700003ff

def z358 : W := mkw 0xffffddfa00408108 0x23ffff77e8010204 0xfffffffe01c081ff 0xe7fffffff8070207

def z359 : W := mkw 0xffe7fff7fffcfffe 0x1fff9fffdffff3ff 0xffe7fffffffcffff 0xffff9ffffffff3ff

def z360 : W := mkw 0xffffdffe08448b6a 0x27ffff7ff821122d 0xfffffffc00008fdf 0xe3fffffff000023f

def z361 : W := mkw 0xfff7fba3fffafdbc 0x1bffdfee8fffebf6 0xffffffe3ffffffff 0xffffffff8fffffff

def z362 : W := mkw 0x53f945d891aa0000 0x214fe5176246a800 0x03f801fc01ff0008 0x040fe007f007fc00

def z363 : W := mkw 0x044b110802113491 0x00112c44200844d2 0x0cfb0000063f702e 0xbc33ec000018fdc0

def z364 : W := mkw 0xfbb460a3f5eac10c 0x13eed1828fd7ab04 0xf304e0e3f9c00001 0x43cc13838fe70000

def z365 : W := mkw 0x0000000000000000 0x0000000000000000 0x0c00000006000026 0x9830000000180000

def z366 : W := mkw 0xfbb40677bdee8b6a 0x07eed019def7ba2d 0xf3241ffff9cc8ffd 0xcfcc907fffe7323f

def z367 : W := mkw 0x044f132e1addbffb 0x04113c4cb86b76ff 0x0cfb111e3ffffffe 0xbc33ec4478ffffff

def z368 : W := mkw 0xfbb0000081200000 0x03eec00002048000 0xfff80003c1f0002f 0x97ffe0000f07c000

def z369 : W := mkw 0x156f177e1addbffb 0x0455bc5df86b76ff 0x33271ffe39ccfffd 0xeccc9c7ff8e733ff

def z370 : W := mkw 0x42c141a08170118c 0x110b05068205c046 0xc3c001e3c1f001eb 0x970f00078f07c007

def z371 : W := mkw 0x1124067618cc8b6a 0x04449019d863322d 0x30201e1e39cc8fe4 0x0cc0807878e7323f

def z372 : W := mkw 0x42c561a6c174d3cc 0x110b15869b05d34f 0xc3e7f1ffc1fcffff 0xff0f9fc7ff07f3ff

def z373 : W := mkw 0xea90000000000000 0x03aa400000000000 0xccd8000000000002 0x0333600000000000

def z374 : W := mkw 0xfbf561a3f5fad18c 0x13efd5868fd7eb46 0xf3c7e1e3f9f0f1fb 0xf7cf1f878fe7c3c7

def z375 : W := mkw 0x42c563a6d9fcdbee 0x150b158e9b67f36f 0xc3c7e1e3f9fcfffb 0xff0f1f878fe7f3ff

def z376 : W := mkw 0x000000208170118c 0x100000008205c046 0x0000000001f001c0 0x040000000007c007

def z377 : W := mkw 0x0000000400040240 0x0000000010001009 0x00000000000c8fe0 0x0c0000000000323f

def z378 : W := mkw 0x044f112e0255b7d9 0x00113c44b80956df 0x0fff11fe07ffffff 0xfc3ffc47f81fffff

def z379 : W := mkw 0x4280000081200000 0x010a000002048000 0xc0c00001c0300002 0x130300000700c000

def z380 : W := mkw 0x0000000000000000 0x0000000000000000 0x3000000238000025 0x88c0000008e00000

def z381 : W := mkw 0xfffbddd800000000 0x23ffef7760000000 0xf307fffc00000011 0x63cc1ffff0000000

def z382 : W := mkw 0xac4fbb0b6e00ec30 0x0ab13eec2db803b0 0xfcffff1ffe00fe3f 0xfbf3fffc7ff803f8

def z383 : W := mkw 0xac4b9b0d2e153ef1 0x0ab12e6c34b854fb 0x3cfb1f1c3e3ffffe 0xbcf3ec7c70f8ffff

def z384 : W := mkw 0x040630024200e410 0x001018c009080390 0xcc07f003c600fe37 0xfb301fc00f1803f8

def z385 : W := mkw 0xfbb00001b5aa0000 0x03eec00006d6a800 0xf3000003ffff0021 0x1fcc00000ffffc00

def z386 : W := mkw 0xfffbddd802002410 0x23ffef7760080090 0xfffffffc0600fe3f 0xfbfffffff01803f8

def z387 : W := mkw 0x4280000081200000 0x010a000002048000 0x03c0000001f00008 0x040f00000007c000

def z388 : W := mkw 0xfbf561a2c170d18c 0x13efd5868b05c346 0xffffe1e3c1f0f1ff 0xf7ffff878f07c3c7

def z389 : W := mkw 0xfbb00001b5aa0000 0x03eec00006d6a800 0xcff80001c7ff000a 0x173fe000071ffc00

def z390 : W := mkw 0xfffbddd9a5220000 0x23ffef7766948800 0xfffffffdc633001f 0xf3fffffff718cc00

def z391 : W := mkw 0x42c563a3ef70fdbc 0x190b158e8fbdc3f6 0xc3c7e1e3fff0fffb 0xff0f1f878fffc3ff

def z392 : W := mkw 0x42c561a2c170d18c 0x110b15868b05c346 0xc3c7e0e3c1f07003 0x730f1f838f07c1c0

def z393 : W := mkw 0xffffffff7eccef7a 0x2ffffffffdfb33bd 0xffffffffffccffff 0xffffffffffff33ff

def z394 : W := mkw 0xac4b110d261536d1 0x02b12c44349854db 0xfcfb111ffe3fffff 0xbff3ec447ff8ffff

def z395 : W := mkw 0xea900001a5220000 0x03aa400006948800 0xc0000001c0000000 0x0300000007000000

def z396 : W := mkw 0x428460a2c160c10c 0x110a11828b058304 0xc304e1e3c1c081f9 0xc70c13878f070207

def z397 : W := mkw 0x000460a24040c10c 0x1000118289010304 0x0004e0e000000000 0x4000138380000000

def z398 : W := mkw 0xfffbdddc00040240 0x23ffef7770001009 0xfffffffc000c8fff 0xeffffffff000323f

def z399 : W := mkw 0xa800000124000000 0x02a0000004900000 0xfcf80003fe3f002f 0x9ff3e0000ff8fc00

def z400 : W := mkw 0xfffbdddc021536d1 0x23ffef77700854db 0xfffffffc0000ffdf 0xe3fffffff00003ff

def z401 : W := mkw 0xfbb0000000000000 0x03eec00000000000 0xfff80000063f002f 0x9fffe0000018fc00

def z402 : W := mkw 0xac06b8024000c000 0x02b01ae009000300 0xfc07fe03c000f037 0xf3f01ff80f0003c0

def z403 : W := mkw 0xbd229e553e8c2e72 0x0ef48a7954fa30b9 0x3c201e1c3e0c0e04 0x08f0807870f83038

def z404 : W := mkw 0x0049010c001512c1 0x000124043000544b 0x00f8011c003f01c8 0x0403e0047000fc07

def z405 : W := mkw 0x53f945f88170118c 0x314fe517e205c046 0x03f801fc01f001c8 0x040fe007f007c007

def z406 : W := mkw 0x53b4067699ee8b6a 0x054ed019da67ba2d 0x33fc1ffe39ff8ffd 0xcccff07ff8e7fe3f

def z407 : W := mkw 0x0000000002002410 0x0000000000080090 0x000000000600fe20 0x18000000001803f8

def z408 : W := mkw 0x0004002200408108 0x0000100088010204 0x030400e201c00001 0x400c100388070000

def z409 : W := mkw 0x0402b80042006410 0x08100ae001080190 0x0003e00000007000 0x20000f80000001c0

def z410 : W := mkw 0xbd26be536e00ec30 0x0af49af94db803b0 0xff27fffffe00fe3f 0xfbfc9ffffff803f8

def z411 : W := mkw 0x004945d800000000 0x2001251760000000 0x000001fc00000000 0x00000007f0000000

def z412 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000063f0020 0x1c0000000018fc00

def z413 : W := mkw 0xbd3e9e7e18cc8b6a 0x26f4fa79f863322d 0x3f3c1ffe39cc8ffd 0xccfcf07ff8e7323f

def z414 : W := mkw 0x4280000081200000 0x010a000002048000 0xcff80003c7ff002f 0x9f3fe0000f1ffc00

def z415 : W := mkw 0x116d077e18dd9beb 0x0445b41df863766f 0x33fc1ffe39ff8ffd 0xcccff07ff8e7fe3f

def z416 : W := mkw 0xbd3a9c5800000000 0x22f4ea7160000000 0xfc3ffe1c00000017 0xe3f0fff870000000

def z417 : W := mkw 0x04021004021536d1 0x00100840100854db 0x0c031000063ffff6 0xbc300c400018ffff

def z418 : W := mkw 0x0004000200008000 0x0000100008000200 0x0004000200008031 0xc000100008000200

def z419 : W := mkw 0x53b0047491ee034a 0x054ec011d247b80d 0x03f801fc01ff01c8 0x040fe007f007fc07

def z420 : W := mkw 0x46cb51ac837537dd 0x111b2d46b20dd4df 0x0ffb11fc07fffffe 0xbc3fec47f01fffff

def z421 : W := mkw 0x1169057c10dd13cb 0x0445a415f043744f 0x03f801fc01ff01c8 0x040fe007f007fc07

def z422 : W := mkw 0x1120045000000000 0x0044801140000000 0x30201e1c00000004 0x00c0807870000000

def z423 : W := mkw 0xac02980126002410 0x0ab00a6004980090 0x0c00000006000000 0x0030000000180000

def z424 : W := mkw 0xac029a012e002c30 0x0ab00a6804b800b0 0xfc001e03fe000e27 0x9bf000780ff80038

def z425 : W := mkw 0xffb6ba036e00ec30 0x0bfedae80db803b0 0xfffffe03fe00fe3f 0xfbfffff80ff803f8

def z426 : W := mkw 0x00042223ef70fdbc 0x180010888fbdc3f6 0x00000003fff0ffe0 0x1c0000000fffc3ff

def z427 : W := mkw 0x000402261addbffb 0x04001008986b76ff 0x000000023fffffe0 0x1c00000008ffffff

def z428 : W := mkw 0x46cb7188c3317495 0x111b2dc6230cc5d2 0xccdbe001c6337002 0x33336f800718cdc0

def z429 : W := mkw 0x044b110c021536d1 0x00112c44300854db 0x0c3b111c060fffd4 0x2830ec4470183fff

def z430 : W := mkw 0xffffffda4a00ec30 0x2bffffff692803b0 0xfffffffc0000fe1f 0xe3fffffff00003f8

def z431 : W := mkw 0xbd269e7618cc8b6a 0x06f49a79d863322d 0xff27fffe39cc8fff 0xeffc9ffff8e7323f

def z432 : W := mkw 0x57fb55d800000000 0x215fed5760000000 0x0ffb11fc0000001e 0xa03fec47f0000000

def z433 : W := mkw 0x0000000000000000 0x0000000000000000 0x00c000000030002a 0x940300000000c000

def z434 : W := mkw 0x00000001a5220000 0x0000000006948800 0x00000001c6330000 0x100000000718cc00

def z435 : W := mkw 0xffba9c5800000000 0x23feea7160000000 0xfff81e1c0000000f 0x83ffe07870000000

def z436 : W := mkw 0xac4b990800000000 0x02b12e6420000000 0xfcffff1c0000001f 0xe3f3fffc70000000

def z437 : W := mkw 0x0004020208008820 0x0000100808200220 0x0000000238008e20 0x0800000008e00238

def z438 : W := mkw 0xffffbb0fffbffef1 0x0bfffeec3ffefffb 0xffffff1fffffffff 0xfffffffc7fffffff

def z439 : W := mkw 0x46cffdfac170d18c 0x311b3ff7eb05c346 0xc3c7ffffc1f0f1fb 0xf70f1fffff07c3c7

def z440 : W := mkw 0x42c1010081301080 0x010b04040204c042 0xc3c30103c1f0f1fb 0xb70f0c040f07c3c7

def z441 : W := mkw 0x040a100c02052651 0x0010284030081499 0x0c38111c060f8ffc 0x8c30e04470183e3f

def z442 : W := mkw 0x156fdffe18cc8b6a 0x2455bf7ff863322d 0x3327fffe39cc8ffd 0xeccc9ffff8e7323f

def z443 : W := mkw 0x0000200166006410 0x0800008005980190 0x00000001c6007000 0x10000000071801c0

def z444 : W := mkw 0x044f310e4215f6d1 0x00113cc4390857db 0xccfff11fc63fffff 0xff33ffc47f18ffff

def z445 : W := mkw 0xfffbddd800000000 0x23ffef7760000000 0x3ff81ffc0000000c 0x00ffe07ff0000000

def z446 : W := mkw 0xfffbdddc001512c1 0x23ffef777000544b 0xfffffffc003f01df 0xe7fffffff000fc07

def z447 : W := mkw 0xbd26be577e8cee72 0x0ef49af95dfa33b9 0xfc27fe1ffe0cfe37 0xfbf09ff87ff833f8

def z448 : W := mkw 0xac06ba036e00ec30 0x0ab01ae80db803b0 0x3c001e03fe00fe24 0x18f000780ff803f8

def z449 : W := mkw 0xa800880000000000 0x02a0022000000000 0xf004ee0000000001 0x43c013b800000000

def z450 : W := mkw 0x0041010000101080 0x0001040400004042 0x000301000000f1d0 0x20000c04000003c7

def z451 : W := mkw 0x152e167e1acdaf7b 0x0454b859f86b36bd 0x3f3c1ffe3fcf8ffd 0xccfcf07ff8ff3e3f

def z452 : W := mkw 0xfffb110800000000 0x03ffec4420000000 0xfffb111c0000001f 0xa3ffec4470000000

def z453 : W := mkw 0xffffffdb6c00c820 0x2bffffff6db00320 0xfffffffff800001f 0xe3ffffffffe00000

def z454 : W := mkw 0xea900001a5220000 0x03aa400006948800 0xfcd80003fe330027 0x9bf360000ff8cc00

def z455 : W := mkw 0x04029a000a002c30 0x08100a68002800b0 0x00001e0000000e00 0x0000007800000038

def z456 : W := mkw 0x11200654188c0a62 0x0444801950623029 0x33201e1e39cc0e2d 0x8ccc807878e73038

def z457 : W := mkw 0xac47bb036e10fcb0 0x0ab11eec0db843f2 0xfcc7ff03fe30ffff 0xfff31ffc0ff8c3ff

def z458 : W := mkw 0x42c561a24050d18c 0x110b158689014346 0xc3c7e1e00000f1db 0xe30f1f87800003c7

def z459 : W := mkw 0x53b044d000000000 0x214ec11340000000 0x030000e000000000 0x000c000380000000

def z460 : W := mkw 0xfbb40673bdea892a 0x07eed019cef7aa24 0xf3040ee3f9c00001 0x43cc103b8fe70000

def z461 : W := mkw 0x0000000000000000 0x0000000000000000 0xc007e00000000013 0xe3001f8000000000

def z462 : W := mkw 0x044b110802113491 0x00112c44200844d2 0x0cdb01000633f1fa 0xb4336c040018cfc7

def z463 : W := mkw 0x42c56182c130d084 0x110b15860b04c342 0xc0c7e003c030f033 0xf3031f800f00c3c0

def z464 : W := mkw 0xfbb4067618cc8b6a 0x07eed019d863322d 0xfffc1ffe39cc8fff 0xcffff07ff8e7323f

def z465 : W := mkw 0x0000020008000820 0x0000000800200020 0x30001e0038000e04 0x08c0007800e00038

def z466 : W := mkw 0xb9300001348a0000 0x02e4c00004d22800 0xfc380003fe0f0027 0x9bf0e0000ff83c00

def z467 : W := mkw 0x46cf71aac170d18c 0x111b3dc6ab05c346 0xcffff1ffc1f0f1ff 0xf73fffc7ff07c3c7

def z468 : W := mkw 0x00040227bdee8b6a 0x040010089ef7ba2d 0x00000003ffff8fe0 0x1c0000000ffffe3f

def z469 : W := mkw 0x044b110c00040240 0x00112c4430001009 0x0cfb111c000c8ffe 0xac33ec447000323f

def z470 : W := mkw 0x1138045800000000 0x2044e01160000000 0x0038001c00000000 0x0000e00070000000

def z471 : W := mkw 0x1120047010c8010a 0x04448011c0432004 0x030000e001c00000 0x000c000380070000

def z472 : W := mkw 0x0447fba24a50fdbc 0x18111fee892943f6 0x0007ffe00000ffd0 0x60001fff800003ff

def z473 : W := mkw 0xbd3a9c5c02052651 0x22f4ea7170081499 0x3c381e1c060f0e04 0x08f0e07870183c38

def z474 : W := mkw 0x57ef77fedbfdffff 0x155fbddffb6ff7ff 0xffffffffffffffff 0xffffffffffffffff

def z475 : W := mkw 0x044b110802113491 0x00112c44200844d2 0x0cdb10000633fe36 0xb8336c400018cff8

def z476 : W := mkw 0x00410104021536d1 0x00010404100854db 0x00c30100063ffffa 0xbc030c040018ffff

def z477 : W := mkw 0x0004022618cc8b6a 0x040010089863322d 0x30041e0239cc8ff5 0xccc0107808e7323f

def z478 : W := mkw 0x000422036c00c820 0x080010880db00320 0x00000003f8000000 0x000000000fe00000

def z479 : W := mkw 0xfbf945d800000000 0x23efe51760000000 0xfff801fc0000000f 0x83ffe007f0000000

def z480 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000100000008e34 0x8800004000000238

def z481 : W := mkw 0xfffffdfac160c10c 0x33fffff7eb058304 0xffffffffc1c0001f 0xe3ffffffff070000

def z482 : W := mkw 0x00452122c170d18c 0x100114848b05c346 0x00c30103c1f0f1fa 0xb4030c040f07c3c7

def z483 : W := mkw 0xfbb00475b5ee034a 0x07eec011d6d7b80d 0xfff801ffffff01ef 0x9fffe007fffffc07

def z484 : W := mkw 0x00042023f5fad18c 0x100010808fd7eb46 0x00000003fffff1e0 0x1c0000000fffffc7

def z485 : W := mkw 0x0049010c001512c1 0x000124043000544b 0x0cf8011c063f01ee 0x9c33e0047018fc07

def z486 : W := mkw 0xbd6fbf7f7eddfffb 0x0ef5befdfdfb77ff 0xffffffffffffffff 0xffffffffffffffff

def z487 : W := mkw 0xa800000124000000 0x02a0000004900000 0xcc000001c6000002 0x1330000007180000

def z488 : W := mkw 0x0000000000000000 0x0000000000000000 0x0020111c0000001c 0x8000804470000000

def z489 : W := mkw 0xbd26be737ec8ed3a 0x0ef49af9cdfb23b4 0xff07fee3ffc0fe37 0xfbfc1ffb8fff03f8

def z490 : W := mkw 0xac4fbb0f6e15fef1 0x0ab13eec3db857fb 0xfc07ff1ffe00fff7 0xfbf01ffc7ff803ff

def z491 : W := mkw 0xfffbfdd8c1305084 0x33ffeff76304c142 0xfffffffdc030701f 0xf3fffffff700c1c0

def z492 : W := mkw 0x42c561a2c170d18c 0x110b15868b05c346 0xc0c7e1e1c030f1d2 0x73031f878700c3c7

def z493 : W := mkw 0x42c16180c1305084 0x110b05860304c142 0xc3c3e003c1f0702b 0xb70f0f800f07c1c0

def z494 : W := mkw 0x044bdddc021536d1 0x20112f77700854db 0x0cfffffc063ffffe 0xfc33fffff018ffff

def z495 : W := mkw 0xa804aa036c00c820 0x0aa012a80db00320 0xfc04ee03fe000027 0xdbf013b80ff80000

def z496 : W := mkw 0x53f561a2d1fad18c 0x114fd5868b47eb46 0xc3ffe1e3c1fff1fb 0xf70fff878f07ffc7

def z497 : W := mkw 0xac02b80166006410 0x0ab00ae005980190 0xfc07fe01c6007017 0xf3f01ff8071801c0

def z498 : W := mkw 0xac02980000000000 0x02b00a6000000000 0x3c001e0000000004 0x00f0007800000000

def z499 : W := mkw 0x044b110802002410 0x00112c4420080090 0x0cfb111c0600fe3e 0xb833ec44701803f8

def z500 : W := mkw 0x156bddd800000000 0x2055af7760000000 0x3327fffc0000001d 0xe0cc9ffff0000000

def z501 : W := mkw 0x044f71ae4255f7dd 0x10113dc6b90957df 0x0cfff1fc063ffffe 0xfc33ffc7f018ffff

def z502 : W := mkw 0x53e565f2c170d18c 0x114f9597cb05c346 0xf3e7ffffc1f0f1ff 0xf7cf9fffff07c3c7

def z503 : W := mkw 0x42c561a2c170d18c 0x110b15868b05c346 0x03c7e1e001f0f1d8 0x640f1f878007c3c7

def z504 : W := mkw 0x044b110c021536d1 0x00112c44300854db 0x0c03111c0600fff6 0xb8300c44701803ff

def z505 : W := mkw 0x53e567f2d9f8d9ae 0x154f959fcb67e366 0xf3c7efe3f9f0f1fb 0xf7cf1fbf8fe7c3c7

def z506 : W := mkw 0x0004020208008820 0x0000100808200220 0x00041e0000008e10 0x4000107800000238

def z507 : W := mkw 0xfbb4aa03fdaac820 0x0beed2a80ff6ab20 0xf304ee03f9c00001 0x43cc13b80fe70000

def z508 : W := mkw 0x1120000010880000 0x0044800000422000 0x3ff800023fff002f 0x9cffe00008fffc00

def z509 : W := mkw 0xa804aa036c00c820 0x0aa012a80db00320 0xf007ee03f800f033 0xf3c01fb80fe003c0

def z510 : W := mkw 0xfffb1109b5aa0000 0x03ffec4426d6a800 0xfffb111fffff003f 0xbfffec447ffffc00

def z511 : W := mkw 0x0004022208408928 0x0000100888210224 0x33041fe239c08ffd 0xcccc107f88e7023f

def z512 : W := mkw 0x00000204188c0a62 0x0400000810623029 0x00000000380c0e00 0x0800000000e03038

def z513 : W := mkw 0xeedbd98800000000 0x23bb6f6620000000 0xccfbf11c0000001e 0xa333efc470000000

def z514 : W := mkw 0xbd26ba037e88ec30 0x0af49ae80dfa23b0 0xff27fe03ffccfe3f 0xfffc9ff80fff33f8

def z515 : W := mkw 0x0041418000000000 0x0001050600000000 0x0007e1e000000010 0x60001f8780000000

def z516 : W := mkw 0xeec7fb836e00ec30 0x0bbb1fee0db803b0 0xffc7ffe3fe00fe3f 0xfbff1fff8ff803f8

def z517 : W := mkw 0x42c541a28170918c 0x110b15068a05c246 0x03c401e201f081f9 0xc40f10078807c207

def z518 : W := mkw 0x11200004108c0240 0x0044800010423009 0x3320111e39cc8ffd 0x8ccc804478e7323f

def z519 : W := mkw 0x428460a2c170d18c 0x110a11828b05c346 0xc304e0e3c1f0f1e1 0x570c13838f07c3c7

def z520 : W := mkw 0x53e561a2d1f8d18c 0x114f95868b47e346 0xf3e7e1e3f9fcf1ff 0xffcf9f878fe7f3c7

def z521 : W := mkw 0xac06ba036e00ec30 0x0ab01ae80db803b0 0xfc07ee03fe007003 0x73f01fb80ff801c0

def z522 : W := mkw 0xbd3a100d368f2651 0x02f4e84034da3c99 0x3c38101c3e0f0e04 0x08f0e04070f83c38

def z523 : W := mkw 0x0004002200408108 0x0000100088010204 0x0000000201c081e0 0x0400000008070207

def z524 : W := mkw 0xffb2b801f7aa6410 0x0bfecae007dea990 0xfffbe003ffff702f 0xbfffef800ffffdc0

def z525 : W := mkw 0x0049010c021536d1 0x00012404300854db 0x00f8011c063fffe8 0x1c03e0047018ffff

def z526 : W := mkw 0x1120047410cc034a 0x04448011d043300d 0x33241ffc01cc01dd 0xc4cc907ff0073007

def z527 : W := mkw 0x0004022618cc8b6a 0x040010089863322d 0x0020111e39cc8ffc 0x8c00804478e7323f

def z528 : W := mkw 0x57fbddd800000000 0x215fef7760000000 0x03fffffc00000018 0x600ffffff0000000

def z529 : W := mkw 0x0000000000000000 0x0000000000000000 0x000300000000f032 0xb0000c00000003c0

def z530 : W := mkw 0xfffbddd9348a0000 0x23ffef7764d22800 0xfffffffc3e0f001f 0xebfffffff0f83c00

def z531 : W := mkw 0x1124020218888820 0x0044900808622220 0x33241e0239cc8e3d 0xcccc907808e73238

def z532 : W := mkw 0x0000000400040240 0x0000000010001009 0x0cf8111c063f8ffe 0x9c33e0447018fe3f

def z533 : W := mkw 0xea84eaa3ed60c92c 0x1baa13aa8fb58324 0xf304eee3f9c00001 0x43cc13bb8fe70000

def z534 : W := mkw 0x0000000000000000 0x0000000000000000 0x00200000000c002c 0x8c00800000003000

def z535 : W := mkw 0xfbb42203ffaaec30 0x0beed0880ffeabb0 0xfff80003fffffe2f 0x9fffe0000ffffff8

def z536 : W := mkw 0xfbf945d9b5aa0000 0x23efe51766d6a800 0xfff801ffffff002f 0x9fffe007fffffc00

def z537 : W := mkw 0xfffbddd802113491 0x23ffef77600844d2 0xfffffffc0633701f 0xf3fffffff018cdc0

def z538 : W := mkw 0x42c941ac817513cd 0x110b2506b205d44f 0x03f801fc01ff01c8 0x040fe007f007fc07

def z539 : W := mkw 0x1120000000000000 0x0044800000000000 0x332000000000000d 0x80cc800000000000

def z540 : W := mkw 0x044bd98800000000 0x20112f6620000000 0x0003e00000000000 0x20000f8000000000

def z541 : W := mkw 0x1120047410cc034a 0x04448011d043300d 0x332001fe39cc01ed 0x8ccc8007f8e73007

def z542 : W := mkw 0xfbf1cdd000000000 0x23efc73740000000 0xf3c7efe00000001b 0xe3cf1fbf80000000

def z543 : W := mkw 0xbd3a9e592e002c30 0x2af4ea7964b800b0 0x3c381e1c3e000e04 0x08f0e07870f80038

def z544 : W := mkw 0xffb6be77ffeeef7a 0x0ffedaf9dfffbbbd 0xffffffffffffffff 0xffffffffffffffff

def z545 : W := mkw 0xeec3f981e7307494 0x1bbb0fe6079cc1d2 0xccc3e001c6307002 0x33330f800718c1c0

def z546 : W := mkw 0xfffbddd891aa0000 0x23ffef776246a800 0xfffffffc01ff001f 0xe7fffffff007fc00

def z547 : W := mkw 0x42c561a3f5fad18c 0x110b15868fd7eb46 0xc3c7e1e3fffff1fb 0xff0f1f878fffffc7

def z548 : W := mkw 0x1124067218c8892a 0x04449019c8632224 0x33240ee239cc002d 0xcccc903b88e73000

def z549 : W := mkw 0xb924ae777ccccb6a 0x0ee492b9ddf3332d 0xf324fffff9cc8ffd 0xcfcc93ffffe7323f

def z550 : W := mkw 0x0000000010880000 0x0000000000422000 0x0000000239cc0020 0x0c00000008e73000

def z551 : W := mkw 0x044b110c021536d1 0x00112c44300854db 0x0003111c063ffff0 0x3c000c447018ffff

def z552 : W := mkw 0x46cb518800000000 0x011b2d4620000000 0xcffff1fc0000001f 0xe33fffc7f0000000

def z553 : W := mkw 0x11200654188c0a62 0x0444801950623029 0x30201f1c380c8ffc 0x8cc0807c70e0323f

def z554 : W := mkw 0x0004022618cc8b6a 0x040010089863322d 0x030401e239cc8ff9 0xcc0c100788e7323f

def z555 : W := mkw 0x1124067618cc8b6a 0x04449019d863322d 0x03241ffc01cc8fd8 0x440c907ff007323f

def z556 : W := mkw 0xa8000001b5aa0000 0x02a0000006d6a800 0xfc000003ffff0027 0x9ff000000ffffc00

def z557 : W := mkw 0x1120000010880000 0x0044800000422000 0x30200000380c0004 0x08c0800000e03000

def z558 : W := mkw 0x00000004021536d1 0x00000000100854db 0x0cf80000063fffee 0x9c33e0000018ffff

def z559 : W := mkw 0x004141a00050118c 0x1001050680014046 0x000001e0000001c0 0x0000000780000007

def z560 : W := mkw 0x0004067608448b6a 0x04001019d821122d 0x30041ffe38008ff5 0xc8c0107ff8e0023f

def z561 : W := mkw 0x0402100002002410 0x0010084000080090 0x0c03000006007002 0x30300c00001801c0

def z562 : W := mkw 0x428040a08160010c 0x110a010282058004 0x030000e001c00000 0x000c000380070000

def z563 : W := mkw 0x1120045400040240 0x0044801150001009 0x33241ffc000c8ffd 0xcccc907ff000323f

def z564 : W := mkw 0xac06ba23ef70fdbc 0x1ab01ae88fbdc3f6 0xfc07fe03fff0fff7 0xfff01ff80fffc3ff

def z565 : W := mkw 0x112426777eccef7a 0x0c449099ddfb33bd 0x33241fffffccfffd 0xdccc907fffff33ff

def z566 : W := mkw 0xb9300001348a0000 0x02e4c00004d22800 0x3000000038000000 0x00c0000000e00000

def z567 : W := mkw 0xac4b990c021536d1 0x02b12e64300854db 0xfcffff1c063fffff 0xfff3fffc7018ffff

def z568 : W := mkw 0x1124067618cc8b6a 0x04449019d863322d 0x032001fe39cc8fe8 0x0c0c8007f8e7323f

def z569 : W := mkw 0x00000001b5aa0000 0x0000000006d6a800 0x00000003f9c00000 0x000000000fe70000

def z570 : W := mkw 0x044b110c021536d1 0x00112c44300854db 0x00c3111c0030fffa 0xb4030c447000c3ff

def z571 : W := mkw 0xb92406773ccc8b6a 0x06e49019dcf3322d 0xff241fffffcc8fff 0xdffc907fffff323f

def z572 : W := mkw 0x0443110002103490 0x00110c44000840d2 0x0cc311000630fffe 0xbc330c440018c3ff

def z573 : W := mkw 0xeec3d98000000000 0x03bb0f6600000000 0xffc7ffe00000001f 0xe3ff1fff80000000

def z574 : W := mkw 0x040a100802012411 0x0010284020080490 0x0c18000006030000 0x0030600000180c00

def z575 : W := mkw 0x044ffdfa4050d18c 0x30113ff7e9014346 0x0007fffc0000f1d0 0x60001ffff00003c7

def z576 : W := mkw 0x0402100002002410 0x0010084000080090 0x0cfb1000063ffe3e 0xbc33ec400018fff8

def z577 : W := mkw 0x044f177e0a55bffb 0x04113c5df82956ff 0x00071ffc0000ffd0 0x60001c7ff00003ff

def z578 : W := mkw 0x11242676d9fcdbee 0x14449099db67f36f 0x33241ffff9fcfffd 0xdccc907fffe7f3ff

def z579 : W := mkw 0xea900001a5220000 0x03aa400006948800 0xccf80001c63f002e 0x9f33e0000718fc00

def z580 : W := mkw 0x42c16180c1305084 0x110b05860304c142 0xc0c3e101c030f1fa 0xb7030f840700c3c7

def z581 : W := mkw 0x0000000402052651 0x0000000010081499 0x00000000060f0e00 0x0800000000183c38

def z582 : W := mkw 0x0406be764a44ef7a 0x0c101af9d92913bd 0x0007fffc0000ffd0 0x60001ffff00003ff

def z583 : W := mkw 0x42c1418000000000 0x010b050600000000 0xc0c3e00000000002 0x23030f8000000000

def z584 : W := mkw 0x53f141a091fa118c 0x114fc5068247e846 0x03f801e001ff01c8 0x040fe0078007fc07

def z585 : W := mkw 0x46cb518c021536d1 0x011b2d46300854db 0xcffff1fc063fffff 0xff3fffc7f018ffff

def z586 : W := mkw 0xa804aa036c00c820 0x0aa012a80db00320 0xf004fe03f8008e35 0xcbc013f80fe00238

def z587 : W := mkw 0x00042022c160c10c 0x100010808b058304 0x00000003c1c00000 0x000000000f070000

def z588 : W := mkw 0xffb2dcd000000000 0x23fecb7340000000 0xff07fee000000017 0xe3fc1ffb80000000

def z589 : W := mkw 0xfbb40023b5ea8108 0x03eed0008ed7aa04 0xfffc01e3ffff81ff 0xdffff0078ffffe07

def z590 : W := mkw 0x0000002410cc034a 0x040000009043300d 0x0000000001cc01c0 0x0400000000073007

def z591 : W := mkw 0x0402100402042650 0x0010084010081099 0x0c23111c060cfffe 0xbc308c44701833ff

def z592 : W := mkw 0x53b0000000000000 0x014ec00000000000 0x03f8000000000008 0x000fe00000000000

def z593 : W := mkw 0x044b110800000000 0x00112c4420000000 0x0cdb000000000002 0x20336c0000000000

def z594 : W := mkw 0xfbb00001b5aa0000 0x03eec00006d6a800 0xff380003ffcf0005 0x0bfce0000fff3c00

def z595 : W := mkw 0xac4fffdb6e00ec30 0x2ab13fff6db803b0 0xfc07fffffe00fe37 0xfbf01ffffff803f8

def z596 : W := mkw 0x044fdffe08448b6a 0x24113f7ff821122d 0x0007fffc00008fd0 0x60001ffff000023f

def z597 : W := mkw 0xac06ba036e00ec30 0x0ab01ae80db803b0 0xfc04fe03fe000e05 0x4bf013f80ff80038

def z598 : W := mkw 0x42c1418000000000 0x010b050600000000 0x03c001e000000008 0x000f000780000000

def z599 : W := mkw 0x1124002210c88108 0x0044900088432204 0x332401e239cc81fd 0xcccc900788e73207

def z600 : W := mkw 0x040612020a00ac30 0x00101848082802b0 0x3c071e023e00fe37 0xf8f01c7808f803f8

def z601 : W := mkw 0xac06ba076e15fef1 0x0ab01ae81db857fb 0xfc07fe03fe3ffff7 0xfff01ff80ff8ffff

def z602 : W := mkw 0xeec7f9a3e770f59c 0x1bbb1fe68f9dc3d6 0xcfc7e1e3c7f0f1fb 0xf73f1f878f1fc3c7

def z603 : W := mkw 0xfbb00001b5aa0000 0x03eec00006d6a800 0xf3c00003f9f0002b 0x97cf00000fe7c000

def z604 : W := mkw 0x0041618040105084 0x1001058601004142 0x0003e00000007000 0x20000f80000001c0

def z605 : W := mkw 0x1120045000000000 0x0044801140000000 0x032001fc00000008 0x000c8007f0000000

def z606 : W := mkw 0x044f130e0a15bef1 0x00113c4c382856fb 0x3cff1f1e3e3fffff 0xfcf3fc7c78f8ffff

def z607 : W := mkw 0x53f945d800000000 0x214fe51760000000 0x33fc1ffc0000001d 0xc0cff07ff0000000

def z608 : W := mkw 0xee96ba03ef22ec30 0x0bba5ae80fbc8bb0 0xfcdffe03fe33fe37 0xfbf37ff80ff8cff8

def z609 : W := mkw 0x0000002000400108 0x0000000080010004 0x030001e001c001c8 0x040c000780070007

def z610 : W := mkw 0x040a100c021536d1 0x00102840300854db 0x0c38101c063fffe4 0x1c30e0407018ffff

def z611 : W := mkw 0xfbb42023f5fad18c 0x13eed0808fd7eb46 0xfff80003fffff1ef 0x9fffe0000fffffc7

def z612 : W := mkw 0xeedffb8b6e00ec30 0x2bbb7fee2db803b0 0xfcdffe03fe00fe37 0xfbf37ff80ff803f8

def z613 : W := mkw 0x42c563a2c970d9ac 0x110b158e8b25c366 0xf3c7ffe3f9f0ffff 0xffcf1fff8fe7c3ff

def z614 : W := mkw 0x42c16180c1305084 0x110b05860304c142 0xc3c7e1e1c030701b 0xf30f1f878700c1c0

def z615 : W := mkw 0xfffbdddc02052651 0x23ffef7770081499 0xfffffffc060f0e1f 0xebfffffff0183c38

def z616 : W := mkw 0xbd36ba037e8aec30 0x0af4dae80dfa2bb0 0xfc3ffe03fe0ffe37 0xfbf0fff80ff83ff8

def z617 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000100000081f8 0x8400000400000207

def z618 : W := mkw 0x42806080c1204004 0x110a018203048100 0xc000e001c0000000 0x0300038007000000

def z619 : W := mkw 0x57fb55dc021536d1 0x215fed57700854db 0x0ffb11fc063ffffe 0xbc3fec47f018ffff

def z620 : W := mkw 0x0406ba036e00ec30 0x08101ae80db803b0 0x0007fe03fe00fe30 0x78001ff80ff803f8

def z621 : W := mkw 0xbd7b9d5800000000 0x22f5ee7560000000 0x3cfb1f1c0000001e 0xa0f3ec7c70000000

def z622 : W := mkw 0x46cf71aec375f7dd 0x111b3dc6bb0dd7df 0xc3c7f1ffc1f0fffb 0xf70f1fc7ff07c3ff

def z623 : W := mkw 0x1124047200408108 0x00449011c8010204 0x33241ffe01c081fd 0xc4cc907ff8070207

def z624 : W := mkw 0xeedbd98c021536d1 0x23bb6f66300854db 0xccfbf11c063ffffe 0xbf33efc47018ffff

def z625 : W := mkw 0x044fffda4a00ec30 0x28113fff692803b0 0x0007fffc0000fe10 0x60001ffff00003f8

def z626 : W := mkw 0x0000000000000000 0x0000000000000000 0x0300000201c00029 0x840c000008070000

def z627 : W := mkw 0xfbb00001b5aa0000 0x03eec00006d6a800 0xfcf80001fe3f0006 0x1bf3e00007f8fc00

def z628 : W := mkw 0xac4bb90d661576d1 0x0ab12ee4359855db 0xccfbf11dc63ffffe 0xbf33efc47718ffff

def z629 : W := mkw 0xeedb110da73736d1 0x03bb6c44369cdcdb 0xccfb111dc63ffffe 0xbf33ec447718ffff

def z630 : W := mkw 0x040a9c5800000000 0x20102a7160000000 0x00001e1c00000000 0x0000007870000000

def z631 : W := mkw 0x0049010c001512c1 0x000124043000544b 0x00fb011c003ff1fa 0xb403ec047000ffc7

def z632 : W := mkw 0x0000000000101080 0x0000000000004042 0x000000000030f1e0 0x140000000000c3c7

def z633 : W := mkw 0x000002012e002c30 0x0800000804b800b0 0x000000003e000e00 0x0800000000f80038

def z634 : W := mkw 0xac029a012e002c30 0x0ab00a6804b800b0 0x3c031e003e00fe36 0xb8f00c7800f803f8

def z635 : W := mkw 0xac02b80166006410 0x0ab00ae005980190 0xcc03f001c600fe36 0xbb300fc0071803f8

def z636 : W := mkw 0xffba9c59b5aa0000 0x23feea7166d6a800 0xfff81e1fffff002f 0x9fffe0787ffffc00

def z637 : W := mkw 0xee92b801e7226410 0x0bba4ae0079c8990 0xccdbe001c6337002 0x33336f800718cdc0

def z638 : W := mkw 0xfbb4eed36c00c820 0x2beed3bb4db00320 0xf304eee3f8000001 0x43cc13bb8fe00000

def z639 : W := mkw 0x0004022218c8892a 0x0400100888632224 0x0000000239c00000 0x0000000008e70000

def z640 : W := mkw 0xffb21001b7aa2410 0x03fec84006dea890 0xfffb1003fffffe3f 0xbfffec400ffffff8

def z641 : W := mkw 0x004561a24050d18c 0x1001158689014346 0x0307e1e201c0f1f9 0xe40c1f87880703c7

def z642 : W := mkw 0xfbb00005b5ae0240 0x03eec00016d6b809 0xfff8111fffff8fff 0x9fffe0447ffffe3f

def z643 : W := mkw 0x0000000000000000 0x0000000000000000 0x0cd8000006330002 0x103360000018cc00

def z644 : W := mkw 0x53b0000091aa0000 0x014ec0000246a800 0x33f8000239ff002d 0x8ccfe00008e7fc00

def z645 : W := mkw 0xb9300001b5aa0000 0x02e4c00006d6a800 0x3c380003ffff0024 0x1cf0e0000ffffc00

def z646 : W := mkw 0xfbb460a3f5eac10c 0x13eed1828fd7ab04 0xfffce0e3ffff002f 0xdffff3838ffffc00

def z647 : W := mkw 0xffffffdf6e15fef1 0x2bffffff7db857fb 0xfffffffffe3fffff 0xfffffffffff8ffff

def z648 : W := mkw 0xfbb00001b5aa0000 0x03eec00006d6a800 0xfff80003f9c0000f 0x83ffe0000fe70000

def z649 : W := mkw 0xfbb00655bdae0a62 0x07eec01956f6b829 0xfff81e1fffff0e2f 0x9fffe0787ffffc38

def z650 : W := mkw 0x044b110c021536d1 0x00112c44300854db 0x0023111c000cfffc 0xac008c44700033ff

def z651 : W := mkw 0xfbb0000000000000 0x03eec00000000000 0xf300000000000001 0x03cc000000000000

def z652 : W := mkw 0xfbb42003f5aac000 0x03eed0800fd6ab00 0xffffe003fffff03f 0xffffff800fffffc0

def z653 : W := mkw 0x044f71ae4255f7dd 0x10113dc6b90957df 0x0007f1fc0000ffd0 0x60001fc7f00003ff

def z654 : W := mkw 0xac06ba036e00ec30 0x0ab01ae80db803b0 0x3c07fe003e00fe14 0x68f01ff800f803f8

def z655 : W := mkw 0x000004740044034a 0x04000011d001100d 0x000001fc000001c0 0x00000007f0000007

def z656 : W := mkw 0x53a4067699ec8b6a 0x054e9019da67b22d 0xf3e41ffff9fc8fff 0xdfcf907fffe7f23f

def z657 : W := mkw 0x1124067218c8892a 0x04449019c8632224 0x33041ee239c08e35 0xc8cc107b88e70238

def z658 : W := mkw 0x1124067618cc8b6a 0x04449019d863322d 0x33040ee239cc8fe1 0x4ccc103b88e7323f

def z659 : W := mkw 0x040a100c02052651 0x0010284030081499 0x0000101c00000e00 0x0000004070000038

def z660 : W := mkw 0xac06ba036e00ec30 0x0ab01ae80db803b0 0xcc03e003fe00fe22 0x3b300f800ff803f8

def z661 : W := mkw 0x044b110c02052651 0x00112c4430081499 0x0cfb111c060f0e1e 0xa833ec4470183c38

def z662 : W := mkw 0x1120000010880000 0x0044800000422000 0x3300000239c00001 0x00cc000008e70000

def z663 : W := mkw 0x0402100002002410 0x0010084000080090 0x0c00100006000e04 0x0830004000180038

def z664 : W := mkw 0x42c141a08170118c 0x110b05068205c046 0x03c301e001f0f1fa 0xb40f0c078007c3c7

def z665 : W := mkw 0xeedbd98800000000 0x23bb6f6620000000 0xfcdffe0000000017 0xe3f37ff800000000

def z666 : W := mkw 0x1124067618cc8b6a 0x04449019d863322d 0x33241efe39cc0e05 0x48cc907bf8e73038

def z667 : W := mkw 0x004521024010d080 0x0001148409004342 0xc0c7e103c030f1fb 0xf7031f840f00c3c7

def z668 : W := mkw 0x152a165c1a8d2e73 0x0454a859706a34b9 0x3c381e1c3e0f0e04 0x08f0e07870f83c38

def z669 : W := mkw 0xffffdffa18c8892a 0x27ffff7fe8632224 0xfffffffe39c0001f 0xe3fffffff8e70000

def z670 : W := mkw 0x040632036e00ec30 0x081018c80db803b0 0x0c031003fe00fe36 0xb8300c400ff803f8

def z671 : W := mkw 0xfffffdfec375f7dd 0x33fffff7fb0dd7df 0xffffffffc7ffffff 0xffffffffff1fffff

def z672 : W := mkw 0x0000045000000000 0x0000001140000000 0x00041ffc00000010 0x4000107ff0000000

def z673 : W := mkw 0xac0eba0f6e05ee71 0x0ab03ae83db817b9 0xfc3ffe1ffe0ffe37 0xfbf0fff87ff83ff8

def z674 : W := mkw 0x0004aa024800c820 0x080012a809200320 0x0004ee0000000000 0x400013b800000000

def z675 : W := mkw 0xfbf567f7fdfedbee 0x17efd59fdff7fb6f 0xffffffffffffffff 0xffffffffffffffff

def z676 : W := mkw 0x11240677bdee8b6a 0x04449019def7ba2d 0x33241fffffff8ffd 0xdccc907ffffffe3f

def z677 : W := mkw 0x156b155c021536d1 0x0055ac55700854db 0x3fff1ffc063fffff 0xfcfffc7ff018ffff

def z678 : W := mkw 0xfbb00001348a0000 0x03eec00004d22800 0xfff800003e0f000f 0x8bffe00000f83c00

def z679 : W := mkw 0xac02100126002410 0x02b0084004980090 0xfc031003fe00fe37 0xbbf00c400ff803f8

def z680 : W := mkw 0xbd269e773eccaf7a 0x0ef49a79dcfb32bd 0x3f241ffe3fcc8ffd 0xccfc907ff8ff323f

def z681 : W := mkw 0x0041010000000000 0x0001040400000000 0x00c301000000001a 0xa0030c0400000000

def z682 : W := mkw 0x00000001348a0000 0x0000000004d22800 0x000000003e0f0000 0x0800000000f83c00

def z683 : W := mkw 0x00042022c170d18c 0x100010808b05c346 0xc007e003c1f0f1f3 0xf7001f800f07c3c7

def z684 : W := mkw 0xac06ba03ffaaec30 0x0ab01ae80ffeabb0 0xfc07fe03fffffe37 0xfff01ff80ffffff8

def z685 : W := mkw 0x1165077618dc9bea 0x0445941dd863726f 0x33e71ffe39fcffff 0xfccf9c7ff8e7f3ff

def z686 : W := mkw 0xac069a0208008820 0x02b01a6808200220 0xfc07fe0238008e37 0xebf01ff808e00238

def z687 : W := mkw 0xffb2980000000000 0x03feca6000000000 0xfffffe000000001f 0xe3fffff800000000

def z688 : W := mkw 0x1120065018880822 0x0444801940622020 0x30000e0038000000 0x00c0003800e00000

def z689 : W := mkw 0x0004067608448b6a 0x04001019d821122d 0x00241ffc000c8ffc 0xcc00907ff000323f

def z690 : W := mkw 0xac0a9a0d2e052e71 0x0ab02a6834b814b9 0x3c381e1c3e0f0e04 0x08f0e07870f83c38

def z691 : W := mkw 0xb9300001348a0000 0x02e4c00004d22800 0x3f3800023fcf002d 0x8cfce00008ff3c00

def z692 : W := mkw 0xffba100db7af2651 0x03fee84036debc99 0xfff8101fffff0e2f 0x9fffe0407ffffc38

def z693 : W := mkw 0x00002000c1305084 0x100000800304c142 0x00000001c0307000 0x100000000700c1c0

def z694 : W := mkw 0xfffbfdd966006410 0x2bffeff765980190 0xfffffffdc600701f 0xf3fffffff71801c0

def z695 : W := mkw 0x0000000124000000 0x0000000004900000 0x00000003fe000020 0x180000000ff80000

def z696 : W := mkw 0xfbb00001b5aa0000 0x03eec00006d6a800 0xffd80003fff30003 0x13ff60000fffcc00

def z697 : W := mkw 0x1120045000000000 0x0044801140000000 0x33040ee000000001 0x40cc103b80000000

def z698 : W := mkw 0xac02980000000000 0x02b00a6000000000 0xcc03e00000000002 0x23300f8000000000

def z699 : W := mkw 0xfffbdfd92e002c30 0x2bffef7f64b800b0 0xfffffffc3e000e1f 0xebfffffff0f80038

def z700 : W := mkw 0x42842002c120c000 0x010a10800b048300 0xc3c7e003c1f0f03b 0xf70f1f800f07c3c0

def z701 : W := mkw 0x11200454108c0242 0x0444801150423009 0x0020001c000c0000 0x0000800070003000

def z702 : W := mkw 0xfffbdfdc188c0a62 0x27ffef7f70623029 0xfffffffc380c0e1f 0xebfffffff0e03038

def z703 : W := mkw 0x00000004021536d1 0x00000000100854db 0x0020111c063ffffc 0x9c0080447018ffff

def z704 : W := mkw 0x0004067618cc8b6a 0x04001019d863322d 0x00041ffe39cc8ff0 0x4c00107ff8e7323f

def z705 : W := mkw 0x0049010800111081 0x0001240420004442 0x00d8000000330000 0x000360000000cc00

def z706 : W := mkw 0x42c561a2c160c10c 0x110b15868b058304 0xc3c7e1e3c1c0001b 0xe30f1f878f070000

def z707 : W := mkw 0xffb2dcd000000000 0x23fecb7340000000 0xff27fffc0000001f 0xe3fc9ffff0000000

def z708 : W := mkw 0xfffbddd800101080 0x23ffef7760004042 0xfffffffc063ff1ff 0xfffffffff018ffc7

def z709 : W := mkw 0x42d561a2c172d18c 0x110b55868b05cb46 0xc3dfe1e3c1f3f1fb 0xf70f7f878f07cfc7

def z710 : W := mkw 0x1124067618cc8b6a 0x04449019d863322d 0x33241ffe39c08fdd 0xc0cc907ff8e7023f

def z711 : W := mkw 0x1124067618cc8b6a 0x04449019d863322d 0x33241ffc39cc8fdc 0x4ccc907ff0e7323f

def z712 : W := mkw 0xfffbddd800101080 0x23ffef7760004042 0xfffffffc0030701f 0xf3fffffff000c1c0

def z713 : W := mkw 0xfffbddd881200000 0x23ffef7762048000 0xfffffffdc030001f 0xf3fffffff700c000

def z714 : W := mkw 0x42c561a2c170d18c 0x110b15868b05c346 0xc307e1e3c1c0f1f9 0xe70c1f878f0703c7

def z715 : W := mkw 0x1120045000000000 0x0044801140000000 0xf327fffc0000001f 0xe3cc9ffff0000000

def z716 : W := mkw 0x044bddd800000000 0x20112f7760000000 0x00c7fffc0000001a 0xe0031ffff0000000

def z717 : W := mkw 0xa8000001b5aa0000 0x02a0000006d6a800 0xfcf80003ffff002f 0x9ff3e0000ffffc00

def z718 : W := mkw 0xeedfdbae18cc8b6a 0x27bb7f6eb863322d 0xccdbe00239cc8fe2 0x2f336f8008e7323f

def z719 : W := mkw 0x46cbddd800000000 0x211b2f7760000000 0x03c7fffc00000018 0x600f1ffff0000000

def z720 : W := mkw 0xbd3ebc7ac170d18c 0x32f4faf1eb05c346 0x3c381e1fc1f0f1e4 0x14f0e0787f07c3c7

def z721 : W := mkw 0x00042226d9eccb6e 0x140010889b67b32d 0x00000003f9cc8fe0 0x0c0000000fe7323f

def z722 : W := mkw 0xfffbddd881220000 0x23ffef7762048800 0xfffffffc0033001f 0xe3fffffff000cc00

def z723 : W := mkw 0xfbb0ccd1b5aa0000 0x23eec33346d6a800 0xfffcffffffff003f 0xdffff3fffffffc00

def z724 : W := mkw 0xb97561a374dad18c 0x12e5d5868dd36b46 0x3c3fe1e03e0ff1d4 0x68f0ff8780f83fc7

def z725 : W := mkw 0x42c561a2c170d18c 0x110b15868b05c346 0xc3c7e1e3c1f0f1d3 0x730f1f878f07c3c7

def z726 : W := mkw 0xfbf9cdd800000000 0x23efe73760000000 0xf3ffeffc0000001b 0xe3cfffbff0000000

def z727 : W := mkw 0x42c561a2c170d18c 0x110b15868b05c346 0xf3c7e1e3f9f0f1ff 0xffcf1f878fe7c3c7

def z728 : W := mkw 0x156f177a1ad9bdbb 0x0455bc5de86b66f6 0x3fdf0ee23ff37003 0x70ff7c3b88ffcdc0

def z729 : W := mkw 0x42c561a2c170d18c 0x110b15868b05c346 0xcfdfe1e3c7f3f1fb 0xf73f7f878f1fcfc7

def z730 : W := mkw 0x00042226c974dbee 0x140010889b25d36f 0x00000003c1f0ffe0 0x140000000f07c3ff

def z731 : W := mkw 0x044bddd800000000 0x20112f7760000000 0xc007fffc00000013 0xe3001ffff0000000

def z732 : W := mkw 0xac02980126002410 0x02b00a6004980090 0xfc07fe03fe00fe37 0xfbf01ff80ff803f8

def z733 : W := mkw 0xfffbddd800000000 0x23ffef7760000000 0xffdffffc00000013 0x63ff7ffff0000000

def z734 : W := mkw 0x044bddd800000000 0x20112f7760000000 0x0c07fffc00000016 0xe0301ffff0000000

def z735 : W := mkw 0xffbadcd800000000 0x23feeb7360000000 0xff3cfffc0000001d 0xc3fcf3fff0000000

def z736 : W := mkw 0xfbb00001b5aa0000 0x03eec00006d6a800 0xfff80003ffff000d 0x0fffe0000ffffc00

def z737 : W := mkw 0xfffbddd800000000 0x23ffef7760000000 0xfffcfffc0000000d 0x43fff3fff0000000

def z738 : W := mkw 0xfffbddd800101080 0x23ffef7760004042 0xfffffffc0000f1df 0xe3fffffff00003c7

def z739 : W := mkw 0xfbf145d000000000 0x03efc51740000000 0xfffffffc0000001f 0xe3fffffff0000000

def z740 : W := mkw 0xfbb8ccd800000000 0x23eee33360000000 0xf33ceefc00000001 0x43ccf3bbf0000000

def z741 : W := mkw 0xfffbddd9b5aa0000 0x23ffef7766d6a800 0xffffffffffc0003f 0xfbffffffffff0000

def z742 : W := mkw 0x42dd61aac170d18c 0x310b7586ab05c346 0xc3dfe1e3c1f0f1fb 0xf70f7f878f07c3c7

def z743 : W := mkw 0xfbb0ccd1b5aa0000 0x23eec33346d6a800 0xf324fffff9cc003d 0xcfcc93ffffe73000

def z744 : W := mkw 0xfffbddd800000000 0x23ffef7760000000 0xfffffffe3800003f 0xebfffffff8e00000

def z745 : W := mkw 0x53f945fc91fc13ce 0x354fe517f247f04f 0x03f801fc01fc01c8 0x040fe007f007f007

def z746 : W := mkw 0xfffbddd924000000 0x23ffef7764900000 0xfffffffdc600001f 0xf3fffffff7180000

def z747 : W := mkw 0x116145d000000000 0x0045851740000000 0x3327fffc0000001d 0xe0cc9ffff0000000

def z748 : W := mkw 0xfbb00001b5aa0000 0x03eec00006d6a800 0xfff80103ffff81ff 0x9fffe0040ffffe07

def z749 : W := mkw 0xfffbddd926002410 0x2bffef7764980090 0xfffffffc0600001f 0xe3fffffff0180000

def z750 : W := mkw 0xeedbddd800000000 0x23bb6f7760000000 0xccfffffc0000001e 0xe333fffff0000000

def z751 : W := mkw 0x1124267658cccb6a 0x04449099d963332d 0xf324fffff9cc8ffd 0xcfcc93ffffe7323f

def z752 : W := mkw 0x42c561a2c170d18c 0x110b15868b05c346 0xc3ffe1e3c1fff1fb 0xf70fff878f07ffc7

def z753 : W := mkw 0xfffbddd924020000 0x23ffef7764900800 0xfffffffc0603001f 0xe3fffffff0180c00

def z754 : W := mkw 0x42842022c160c108 0x010a10808b058304 0xc3c7e1e3c1f0f1fb 0xf70f1f878f07c3c7

def z755 : W := mkw 0xfbb00001b5aa0000 0x03eec00006d6a800 0xfff80003ffff000b 0x17ffe0000ffffc00

def z756 : W := mkw 0x0004022608448b68 0x000010089821122d 0x33241ffe39cc8ffd 0xcccc907ff8e7323f

def z757 : W := mkw 0xac06ba036e00ec30 0x0ab01ae80db803b0 0xfc27fe03fe0cfe3f 0xfff09ff80ff833f8

def z758 : W := mkw 0xfffbddd802113491 0x23ffef77600844d2 0xfffffffc0633fe3f 0xfbfffffff018cff8

def z759 : W := mkw 0xfffbddd891aa0000 0x23ffef776246a800 0xfffffffc07ff003f 0xfffffffff01ffc00

def z760 : W := mkw 0xbd22bc7576cc675a 0x0ef48af1d5db319d 0xcf23e1fdc7cc71ca 0x373c8f87f71f31c7

def z761 : W := mkw 0x156bddd810880000 0x2055af7760422000 0x3327fffe39cc003d 0xeccc9ffff8e73000

def z762 : W := mkw 0xfffbddd9b5aa0000 0x23ffef7766d6a800 0xf307fffff9c00011 0x63cc1fffffe70000

def z763 : W := mkw 0xac06ba236e40ed38 0x0ab01ae88db903b4 0xfc07ffe3fe00fff7 0xfbf01fff8ff803ff

def z764 : W := mkw 0xfffbddd9a5220000 0x23ffef7766948800 0xfffffffdc000001f 0xe3fffffff7000000

def z765 : W := mkw 0x044bddd800000000 0x20112f7760000000 0x0307fffc00000019 0xe00c1ffff0000000

def z766 : W := mkw 0xfffbddd800000000 0x23ffef7760000000 0xffffffffc000003f 0xf3ffffffff000000

def z767 : W := mkw 0xffbadcd800000000 0x23feeb7360000000 0xfffcfefc0000000f 0xc3fff3fbf0000000

def z768 : W := mkw 0x044b110c021536d1 0x00112c44300854db 0x3cff1f1c063fffff 0xfcf3fc7c7018ffff

def z769 : W := mkw 0x11200001b5aa0000 0x0044800006d6a800 0x3ff80003ffff002f 0x9cffe0000ffffc00

def z770 : W := mkw 0xfbb0ccd000000000 0x23eec33340000000 0xf324effc00000009 0x43cc93bff0000000

def z771 : W := mkw 0x044b990c021536d1 0x00112e64300854db 0x0cffff1c063ffffe 0xfc33fffc7018ffff

def z772 : W := mkw 0xfffb110db7bf36d1 0x03ffec4436defcdb 0xf303111ff9c0ffd1 0x23cc0c447fe703ff

def z773 : W := mkw 0x468e70aec365e75d 0x111a39c2bb0d979d 0xcf3cf0ffc7cf0e05 0x4b3cf3c3ff1f3c38

def z774 : W := mkw 0x42c1418081301080 0x010b05060204c042 0xc3c7e1e3c1f0f1fb 0xf70f1f878f07c3c7

def z775 : W := mkw 0x42c161a0c170518c 0x110b05868305c146 0xc3c7e1e1c1f071db 0xf70f1f878707c1c7

def z776 : W := mkw 0xeecbf989e7317495 0x1bbb2fe6279cc5d2 0xccdbe001c6337002 0x33336f800718cdc0

def z777 : W := mkw 0x42c563a2c970d9ac 0x110b158e8b25c366 0xc3c7e1e3f9f0fffb 0xff0f1f878fe7c3ff

def z778 : W := mkw 0xeedbddd800000000 0x23bb6f7760000000 0xfcdffffc00000017 0xe3f37ffff0000000

def z779 : W := mkw 0xac06ba036e00ec30 0x0ab01ae80db803b0 0xfcdffe03fe33fe37 0xfbf37ff80ff8cff8

def z780 : W := mkw 0xac4bddd800000000 0x22b12f7760000000 0xfcfffffc0000001f 0xe3f3fffff0000000

def z781 : W := mkw 0x46dbddd800000000 0x211b6f7760000000 0x00dffffc00000010 0x60037ffff0000000

def z782 : W := mkw 0xfffbddd800000000 0x23ffef7760000000 0xfffffffc0000f03f 0xf3fffffff00003c0

def z783 : W := mkw 0xfffbddd9348a0000 0x23ffef7764d22800 0xfffffffc3800001f 0xe3fffffff0e00000

def z784 : W := mkw 0x0049cdd800000000 0x2001273760000000 0x0004effc00000000 0x400013bff0000000

def z785 : W := mkw 0x11200454108c0240 0x0044801150423009 0x33241ffe39cc8ffd 0xcccc907ff8e7323f

def z786 : W := mkw 0xfbb0ccd4021536d1 0x23eec333500854db 0xf304eee0063fffe1 0x5fcc13bb8018ffff

def z787 : W := mkw 0xfbb00001b5aa0000 0x03eec00006d6a800 0xcff80003ffff002a 0x1f3fe0000ffffc00

def z788 : W := mkw 0xac06ba036e00ec30 0x0ab01ae80db803b0 0xf007fe03f800fe33 0xf3c01ff80fe003f8

def z789 : W := mkw 0x1124067618cc8b6a 0x04449019d863322d 0x33241ffe3fff8ffd 0xdccc907ff8fffe3f

def z790 : W := mkw 0xfbb0c881b5aa0000 0x23eec32206d6a800 0xfff8e003ffff002f 0x9fffe3800ffffc00

def z791 : W := mkw 0xac06ba036e00ec30 0x0ab01ae80db803b0 0xf007fe03f800fe35 0xebc01ff80fe003f8

def z792 : W := mkw 0x044b110c021536d1 0x00112c44300854db 0x0fff11fc063fffff 0xfc3ffc47f018ffff

def z793 : W := mkw 0xea900001b5aa0000 0x03aa400006d6a800 0xccf80003ffff002e 0x9f33e0000ffffc00

def z794 : W := mkw 0x044bddd802002410 0x20112f7760080090 0x0007fffc0000fe10 0x60001ffff00003f8

def z795 : W := mkw 0xac02ba016e006c30 0x0ab00ae805b801b0 0xfc03fe01fe00fe36 0xbbf00ff807f803f8

def z796 : W := mkw 0xfffbddd800000000 0x23ffef7760000000 0xfffffffc000c003f 0xeffffffff0003000

def z797 : W := mkw 0x42c561a2c170d18c 0x110b15868b05c346 0xc3c7e1e3c1c0f1db 0xe30f1f878f0703c7

def z798 : W := mkw 0xfffbddd9a5220000 0x23ffef7766948800 0xfffffffffe33003f 0xfbfffffffff8cc00

def z799 : W := mkw 0x044bddd9b5aa0000 0x20112f7766d6a800 0x0007ffffffff0030 0x7c001ffffffffc00

def z800 : W := mkw 0x42c561a24040c108 0x010b158689010304 0xc3c7e1e3c1c0f1fb 0xf70f1f878f0703c7

def z801 : W := mkw 0x156bddd800000000 0x2055af7760000000 0x0327fffc00000018 0x600c9ffff0000000

def z802 : W := mkw 0x1124267658cccb6a 0x04449099d963332d 0x3327fffe39ccfffd 0xeccc9ffff8e733ff

def z803 : W := mkw 0x044b110c021536d1 0x00112c44300854db 0x0cf8111c063fffec 0x1c33e0447018ffff

def z804 : W := mkw 0x53e167d4d9bc5ae6 0x154f859f5366f16b 0xf0e3fe1df83c7e06 0x3bc38ff877e0f1f8

def z805 : W := mkw 0x42c561a2c170d18c 0x110b15868b05c346 0xc3c7f1e3c1f0ffff 0xff0f1fc78f07c3ff

def z806 : W := mkw 0xea940677ad668b6a 0x07aa5019deb59a2d 0xccdc1ffdc6338fd2 0x5333707ff718ce3f

def z807 : W := mkw 0xeecbd98800000000 0x03bb2f6620000000 0xfffffffc0000001f 0xe3fffffff0000000

def z808 : W := mkw 0x42cd61aac170d18c 0x110b3586ab05c346 0xc3ffe1ffc1f0f1fb 0xf70fff87ff07c3c7

def z809 : W := mkw 0x0004222658cccb6a 0x040010889963332d 0x00000003f9ccffe0 0x1c0000000fe733ff

def z810 : W := mkw 0x000422265accef7a 0x0c001088996b33bd 0x0000000239ccffe0 0x0c00000008e733ff

def z811 : W := mkw 0x53fd67db6e00ec30 0x294ff59f6db803b0 0x03f801fffe00fe28 0x180fe007fff803f8

def z812 : W := mkw 0x040632024a00ec30 0x001018c8092803b0 0xfc07fe03fe00fe37 0xfbf01ff80ff803f8

def z813 : W := mkw 0xfffbddd810880000 0x23ffef7760422000 0xfffffffc380c001f 0xebfffffff0e03000

def z814 : W := mkw 0xea900001b5aa0000 0x03aa400006d6a800 0xfcd80003ffff0027 0x9ff360000ffffc00

def z815 : W := mkw 0x57b6ba02dbaaec30 0x095edae80b6eabb0 0x03fffe0001fffe18 0x640ffff80007fff8

def z816 : W := mkw 0xac4bddd924000000 0x22b12f7764900000 0xfc07fffffe000037 0xfbf01ffffff80000

def z817 : W := mkw 0x1124067618cc8b6a 0x04449019d863322d 0x33fc1ffe39ff8ffd 0xcccff07ff8e7fe3f

def z818 : W := mkw 0xfffbddd881301080 0x23ffef776204c042 0xffffffffc1f0f1ff 0xf7ffffffff07c3c7

def z819 : W := mkw 0x53e145d091a80000 0x014f85174246a000 0xf3e7fffff9fc003f 0xffcf9fffffe7f000

def z820 : W := mkw 0x044b110c021536d1 0x00112c44300854db 0x0cfb111c063fffda 0x3433ec447018ffff

def z821 : W := mkw 0xeec3dba1af703dbc 0x1bbb0f6e86bdc0f6 0x3fc01fe03ff00fcc 0x0cff007f80ffc03f

def z822 : W := mkw 0xfbb4ae73fdeac92a 0x0feed2b9cff7ab24 0xf304eee3f9c00001 0x43cc13bb8fe70000

def z823 : W := mkw 0x044bddd800000000 0x20112f7760000000 0x00fffffc00000018 0x6003fffff0000000

def z824 : W := mkw 0x044b110c021536d1 0x00112c44300854db 0xccfff11c063fffff 0xff33ffc47018ffff

def z825 : W := mkw 0xfffbddd802113491 0x23ffef77600844d2 0xfffffffc0633f1ff 0xf7fffffff018cfc7

def z826 : W := mkw 0x040adcd800000000 0x20102b7360000000 0x0004fefc00000000 0x400013fbf0000000

def z827 : W := mkw 0x53f9cdd800000000 0x214fe73760000000 0x03fceffc00000008 0x400ff3bff0000000

def z828 : W := mkw 0xbd7bddd800000000 0x22f5ef7760000000 0x3f3ffffc0000001d 0xe0fcfffff0000000

def z829 : W := mkw 0xbd3a9c5800000000 0x22f4ea7160000000 0xff3ffffc0000001f 0xe3fcfffff0000000

def z830 : W := mkw 0xbd7bddd800000000 0x22f5ef7760000000 0xfc3ffffc00000017 0xe3f0fffff0000000

def z831 : W := mkw 0xb920000134880000 0x02e4800004d22000 0xfff80003ffff002f 0x9fffe0000ffffc00

def z832 : W := mkw 0xbd3a9e5d3e8c2e72 0x2ef4ea7974fa30b9 0x3c381e1c3e0c0e04 0x08f0e07870f83038

def z833 : W := mkw 0x0000ccd000000000 0x2000033340000000 0x0004fffc00000010 0x400013fff0000000

def z834 : W := mkw 0xb9208c5000000000 0x02e4823140000000 0xf324fffc0000001d 0xc3cc93fff0000000

def z835 : W := mkw 0xfffbddd9a5220000 0x23ffef7766948800 0xffffffffc7f3003f 0xf7ffffffff1fcc00

def z836 : W := mkw 0x57ebddd800000000 0x215faf7760000000 0xf3e7fffc0000001f 0xe3cf9ffff0000000

def z837 : W := mkw 0x42c161a0c170518c 0x110b05868305c146 0xc3c3e1e1c1f0f1fa 0xb70f0f878707c3c7

def z838 : W := mkw 0x044bddd800000000 0x20112f7760000000 0x0c3ffffc00000014 0x6030fffff0000000

def z839 : W := mkw 0xfffbddd924000000 0x23ffef7764900000 0xfffffffc3e00001f 0xebfffffff0f80000

def z840 : W := mkw 0xac06ba036e00ec30 0x0ab01ae80db803b0 0xfcc7fe03fe30fe3f 0xfff31ff80ff8c3f8

def z841 : W := mkw 0x42c561a2c170d18c 0x110b15868b05c346 0xcfc7e1e3c7f0f1ff 0xff3f1f878f1fc3c7

def z842 : W := mkw 0x1124067618cc8b6a 0x04449019d863322d 0x3ffc1ffe39cc8fff 0xccfff07ff8e7323f

def z843 : W := mkw 0xfffbddd8108a0000 0x23ffef7760422800 0xfffffffc000f001f 0xe3fffffff0003c00

def z844 : W := mkw 0x42c563a2c970d9ac 0x110b158e8b25c366 0xf3c7efe3f9f0f1fb 0xf7cf1fbf8fe7c3c7

def z845 : W := mkw 0xbd7bddd800000000 0x22f5ef7760000000 0x3007fffc00000010 0x60c01ffff0000000

def z846 : W := mkw 0xeedbd989a7333491 0x23bb6f66269cccd2 0xccdbe001c6337002 0x33336f800718cdc0

def z847 : W := mkw 0x1120ccd000000000 0x2044833340000000 0x3324fffc0000001d 0xc0cc93fff0000000

def z848 : W := mkw 0xfffbddd881200000 0x23ffef7762048000 0xfffffffc01f0001f 0xe7fffffff007c000

def z849 : W := mkw 0x000422277eddfffb 0x0c0010889dfb77ff 0x00000003ffffffe0 0x1c0000000fffffff

def z850 : W := mkw 0xfffbddd9a5220000 0x23ffef7766948800 0xfffffffdc63f003f 0xfffffffff718fc00

def z851 : W := mkw 0x00042227ef75fffd 0x180010889fbdd7ff 0x00000003ffffffe0 0x1c0000000fffffff

def z852 : W := mkw 0xfffbddd9a7333491 0x23ffef77669cccd2 0xfffffffdc633701f 0xf3fffffff718cdc0

def z853 : W := mkw 0xfffbddd800000000 0x23ffef7760000000 0xfcfffffc00000016 0x63f3fffff0000000

def z854 : W := mkw 0xfffbddd800000000 0x23ffef7760000000 0xcffffffc0000001a 0x633ffffff0000000

def z855 : W := mkw 0xffb29c51b5aa0000 0x03feca7146d6a800 0xffffffffffff003f 0xfffffffffffffc00

def z856 : W := mkw 0xfffbddd810880000 0x23ffef7760422000 0xfffffffc01cc001f 0xe7fffffff0073000

def z857 : W := mkw 0x0049010c021536d1 0x00012404300854db 0x0cf8011c063fffee 0x9c33e0047018ffff

def z858 : W := mkw 0xac06ba036e00ec30 0x0ab01ae80db803b0 0xfc07fe03fe007e07 0x7bf01ff80ff801f8

def z859 : W := mkw 0x044bddd800101080 0x20112f7760004042 0x00c7fffc0030f1fa 0xf4031ffff000c3c7

def z860 : W := mkw 0x42cd61aac171d18d 0x110b3586ab05c746 0xc3dfe1e3c1f3f1fb 0xf70f7f878f07cfc7

def z861 : W := mkw 0x00042227fdfedbee 0x140010889ff7fb6f 0x00000003ffffffe0 0x1c0000000fffffff

def z862 : W := mkw 0x1120067418cc0b6a 0x04448019d063302d 0x33201ffe39cc0fed 0x8ccc807ff8e7303f

def z863 : W := mkw 0xfffbddd9b5aa0000 0x23ffef7766d6a800 0xfffffffff9f0003f 0xf7ffffffffe7c000

def z864 : W := mkw 0x044bddd800000000 0x20112f7760000000 0x0cdffffc00000012 0x60337ffff0000000

def z865 : W := mkw 0xa84dab0f6c15dae1 0x0aa136ac3db0576b 0xf0fcef1ff83f01c9 0x47c3f3bc7fe0fc07

def z866 : W := mkw 0xac4bddd800000000 0x22b12f7760000000 0x3c07fffc00000014 0x60f01ffff0000000

def z867 : W := mkw 0xfffbddd9348a0000 0x23ffef7764d22800 0xfffffffc3e3f003f 0xfffffffff0f8fc00

def z868 : W := mkw 0x156bddd800000000 0x2055af7760000000 0x3307fffc00000011 0x60cc1ffff0000000

def z869 : W := mkw 0xfffbddd9b5aa0000 0x23ffef7766d6a800 0xfffffffdfe3f001f 0xfbfffffff7f8fc00

def z870 : W := mkw 0xfffbddd802002410 0x23ffef7760080090 0xfffffffc0000fe1f 0xe3fffffff00003f8

def z871 : W := mkw 0xac06ba036e00ec30 0x0ab01ae80db803b0 0xfcfffe03fe00fe3f 0xfbf3fff80ff803f8

def z872 : W := mkw 0x42c561a2c170d18c 0x110b15868b05c346 0xf3c7ffe3c1f0f1ff 0xf7cf1fff8f07c3c7

def z873 : W := mkw 0x00042227fffcfffe 0x1c0010889ffff3ff 0x00000003fffcffe0 0x1c0000000ffff3ff

def z874 : W := mkw 0xfbf9cdd800000000 0x23efe73760000000 0xfffceffc0000000f 0xc3fff3bff0000000

def z875 : W := mkw 0xfffbddd802113491 0x23ffef77600844d2 0xfffffffc063f703f 0xfffffffff018fdc0

def z876 : W := mkw 0xfffbddd810880000 0x23ffef7760422000 0xfffffffe3fff003f 0xfffffffff8fffc00

def z877 : W := mkw 0xfbb08c51b5aa0000 0x23eec23146d6a800 0xfff80e03ffff002f 0x9fffe0380ffffc00

def z878 : W := mkw 0xfbb044d1b5aa0000 0x23eec11346d6a800 0xfff800e3ffff002f 0x9fffe0038ffffc00

def z879 : W := mkw 0x044b110c021536d1 0x00112c44300854db 0x3cfb111e3e3fffff 0xbcf3ec4478f8ffff

def z880 : W := mkw 0xfffbddd924000000 0x23ffef7764900000 0xfffffffff800001f 0xe3ffffffffe00000

def z881 : W := mkw 0xfffbddd800000000 0x23ffef7760000000 0xfffffffe01c0003f 0xe7fffffff8070000

def z882 : W := mkw 0xfffbddd881200000 0x23ffef7762048000 0xffffffffc1c0001f 0xe3ffffffff070000

def z883 : W := mkw 0xfffbddd891a80000 0x23ffef776246a000 0xfffffffff9fc003f 0xffffffffffe7f000

def z884 : W := mkw 0xac5bddd800000000 0x22b16f7760000000 0x0c1ffffc00000010 0x60307ffff0000000

def z885 : W := mkw 0x000422264a44ef7a 0x0c001088992913bd 0x000000000000ffc0 0x00000000000003ff

def z886 : W := mkw 0x040a100c021536d1 0x00102840300854db 0x0cf8101c063fffee 0x9c33e0407018ffff

def z887 : W := mkw 0xfffbddd802012411 0x23ffef7760080490 0xfffffffc0603001f 0xe3fffffff0180c00

def z888 : W := mkw 0x42c561a2c170d18c 0x110b15868b05c346 0xcfffe1e3c1f0f1ff 0xf73fff878f07c3c7

def z889 : W := mkw 0xfffbddd800000000 0x23ffef7760000000 0xfffffffc060f001f 0xebfffffff0183c00

def z890 : W := mkw 0xbd3a9c5d368f2651 0x22f4ea7174da3c99 0x3c381e1c3e0f0e04 0x08f0e07870f83c38

def z891 : W := mkw 0xfffbddd891aa0000 0x23ffef776246a800 0xfffffffe39ff003f 0xeffffffff8e7fc00

def z892 : W := mkw 0xac029c5000000000 0x02b00a7140000000 0xfc07fffc00000017 0xe3f01ffff0000000

def z893 : W := mkw 0xfffbddd9b5aa0000 0x23ffef7766d6a800 0xfffffffdc7ff001f 0xf7fffffff71ffc00

def z894 : W := mkw 0xfffbddd800000000 0x23ffef7760000000 0x3ffffffc0000001c 0x60fffffff0000000

def z895 : W := mkw 0x00000001b5aa0000 0x0000000006d6a800 0x0cd80003ffff0022 0x1c3360000ffffc00

def z896 : W := mkw 0xfffbddd800000000 0x23ffef7760000000 0xfffffffc003f001f 0xe7fffffff000fc00

def z897 : W := mkw 0x53f945dc91bf12c1 0x214fe5177246fc4b 0x03f801fc01ff01c8 0x040fe007f007fc07

def z898 : W := mkw 0xac06ba036e00ec30 0x0ab01ae80db803b0 0xfc07ee03fe00fe23 0x7bf01fb80ff803f8

def z899 : W := mkw 0x1124067618cc8b6a 0x04449019d863322d 0x33041ffe39c08ff5 0xc8cc107ff8e7023f

def z900 : W := mkw 0x1134067618ce8b6a 0x0444d019d8633a2d 0x333c1ffe39cf8ffd 0xccccf07ff8e73e3f

def z901 : W := mkw 0xeecbddd800000000 0x23bb2f7760000000 0xffc7fffc0000001f 0xe3ff1ffff0000000

def z902 : W := mkw 0xfffbddd802113491 0x23ffef77600844d2 0xfffffffc0000701f 0xe3fffffff00001c0

def z903 : W := mkw 0xac06ba036e00ec30 0x0ab01ae80db803b0 0xfc07fe03f800fe17 0xe3f01ff80fe003f8

def z904 : W := mkw 0xfffbddd810880000 0x23ffef7760422000 0xfffffffe39c0001f 0xe3fffffff8e70000

def z905 : W := mkw 0x1120067418cc0b6a 0x04448019d063302d 0x33201ffc39cc8ffc 0x8ccc807ff0e7323f

def z906 : W := mkw 0xfffbddd802002410 0x23ffef7760080090 0xfffffffc0600701f 0xf3fffffff01801c0

def z907 : W := mkw 0xfbb00001b5aa0000 0x03eec00006d6a800 0xfffc1e03ffff003f 0xdffff0780ffffc00

def z908 : W := mkw 0xfffbddd9348a0000 0x23ffef7764d22800 0xfffffffffe0f003f 0xfbfffffffff83c00

def z909 : W := mkw 0xfbf1cdd000000000 0x23efc73740000000 0xf3e7fffc0000001f 0xe3cf9ffff0000000

def z910 : W := mkw 0x11242656588cca62 0x0444909959623329 0xf027fe1ff80cfe37 0xfbc09ff87fe033f8

def z911 : W := mkw 0xfffbddd9a5200000 0x23ffef7766948000 0xfffffffffff0003f 0xffffffffffffc000

def z912 : W := mkw 0xbd7bddd9348a0000 0x22f5ef7764d22800 0x3c3ffffc3e0f0014 0x68f0fffff0f83c00

def z913 : W := mkw 0x42c563a2c970d9ac 0x110b158e8b25c366 0xc3c7ffe3c1f0fffb 0xf70f1fff8f07c3ff

def z914 : W := mkw 0xfffbddd934880000 0x23ffef7764d22000 0xffffffffffcc003f 0xffffffffffff3000

def z915 : W := mkw 0xfbb00001b5aa0000 0x03eec00006d6a800 0xffd80003ffff0023 0x1fff60000ffffc00

def z916 : W := mkw 0xfffbddd891aa0000 0x23ffef776246a800 0xffffffffc1ff003f 0xf7ffffffff07fc00

def z917 : W := mkw 0xfbb0ccd000000000 0x23eec33340000000 0xf324fefc00000005 0x43cc93fbf0000000

def z918 : W := mkw 0xac06ba036e00ec30 0x0ab01ae80db803b0 0xf007fe03fe00fe31 0x7bc01ff80ff803f8

def z919 : W := mkw 0xfbb42227fdfedbee 0x17eed0889ff7fb6f 0xfff80003ffffffef 0x9fffe0000fffffff

def z920 : W := mkw 0x42c543a2897099ac 0x110b150e8a25c266 0x33c41fe239f08ffd 0xcccf107f88e7c23f

def z921 : W := mkw 0x1124067618cc8b6a 0x04449019d863322d 0x33e41ffe39fc8fff 0xdccf907ff8e7f23f

def z922 : W := mkw 0x42c561a2c170d18c 0x110b15868b05c346 0xc3c7e1e3c1f0f1d9 0x670f1f878f07c3c7

def z923 : W := mkw 0xac06ba036e00ec30 0x0ab01ae80db803b0 0xfc07fe03fe00fe13 0x73f01ff80ff803f8

def z924 : W := mkw 0xac06ba036e00ec30 0x0ab01ae80db803b0 0xff07fe03ffc0fe3f 0xfffc1ff80fff03f8

def z925 : W := mkw 0x57fbddd800000000 0x215fef7760000000 0x33fffffc0000001d 0xe0cffffff0000000

def z926 : W := mkw 0xac06ba036e00ec30 0x0ab01ae80db803b0 0xfc07fe03fe00fe15 0x6bf01ff80ff803f8

def z927 : W := mkw 0x53a42226d9fcdbee 0x154e90889b67f36f 0xf3e00003f9fcffef 0x9fcf80000fe7f3ff

def z928 : W := mkw 0x42c561a2c170d18c 0x110b15868b05c346 0xc3c7e1e3c1f071cb 0x770f1f878f07c1c7

def z929 : W := mkw 0xfffbddd9b5aa0000 0x23ffef7766d6a800 0xfffffffff9cc003f 0xefffffffffe73000

def z930 : W := mkw 0x044f77fe4a55ffff 0x14113ddff92957ff 0x0007fffc0000ffd0 0x60001ffff00003ff

def z931 : W := mkw 0x044bddd802113491 0x20112f77600844d2 0x0007fffc00007010 0x60001ffff00001c0

def z932 : W := mkw 0xfffbddd926002410 0x23ffef7764980090 0xfffffffffe00fe3f 0xfbfffffffff803f8

def z933 : W := mkw 0xeedbddd800000000 0x23bb6f7760000000 0xcfdffffc0000001b 0xe33f7ffff0000000

def z934 : W := mkw 0x044bddd802002410 0x20112f7760080090 0x0c07fffc0600fe36 0xf8301ffff01803f8

def z935 : W := mkw 0xfbf9cdd800000000 0x23efe73760000000 0xf3fcfffc0000001d 0xc3cff3fff0000000

def z936 : W := mkw 0xfbb00451b5aa0000 0x03eec01146d6a800 0xfff81e1fffff002f 0x9fffe0787ffffc00

def z937 : W := mkw 0xfbb00001b5aa0000 0x03eec00006d6a800 0xfff8111fffff003f 0x9fffe0447ffffc00

def z938 : W := mkw 0x1124067618cc8b6a 0x04449019d863322d 0x33201ffe39cc8fec 0x0ccc807ff8e7323f

def z939 : W := mkw 0xac02ba016e006c30 0x0ab00ae805b801b0 0xfc07fe01fe007e17 0xfbf01ff807f801f8

def z940 : W := mkw 0x42c561a2c170d18c 0x110b15868b05c346 0xc3c7e0e3c1f0f1e3 0x770f1f838f07c3c7

def z941 : W := mkw 0x53b00001b5aa0000 0x014ec00006d6a800 0x0ff80003ffff002e 0x9c3fe0000ffffc00

def z942 : W := mkw 0x044bddd800101080 0x20112f7760004042 0x0007fffc0000f1d0 0x60001ffff00003c7

def z943 : W := mkw 0xeedbf989e7307494 0x3bbb6fe6279cc1d2 0xccdbe001c6307002 0x33336f800718c1c0

def z944 : W := mkw 0xfffbddd800000000 0x23ffef7760000000 0xf327fffc0000001d 0xe3cc9ffff0000000

def z945 : W := mkw 0xfffbddd802002410 0x23ffef7760080090 0xfffffffc063ffe3f 0xfffffffff018fff8

def z946 : W := mkw 0x42c561a2c170d18c 0x110b15868b05c346 0xc307e1e3c1c0f1f3 0xf30c1f878f0703c7

def z947 : W := mkw 0x004561a24050d18c 0x1001158689014346 0xc307e1e3c1c0f1fb 0xf70c1f878f0703c7

def z948 : W := mkw 0x1124067208408928 0x00449019c8210224 0x33241ffe39c08ffd 0xcccc907ff8e7023f

def z949 : W := mkw 0xfffbddd800000000 0x23ffef7760000000 0xffffeffc0000000b 0x63ffffbff0000000

def z950 : W := mkw 0xac0eba0b6e01ec31 0x0ab03ae82db807b0 0xfc1ffe03fe03fe37 0xfbf07ff80ff80ff8

def z951 : W := mkw 0xbd6bddd800000000 0x22f5af7760000000 0xff27fffc0000001f 0xe3fc9ffff0000000

def z952 : W := mkw 0x044bddd800000000 0x20112f7760000000 0x3007fffc00000015 0xe0c01ffff0000000

def z953 : W := mkw 0xfffbddd9b5aa0000 0x23ffef7766d6a800 0xfffffffffff3001f 0xf3ffffffffffcc00

def z954 : W := mkw 0x1124067618cc8b6a 0x04449019d863322d 0x33041ffe39cc8ff1 0x4ccc107ff8e7323f

def z955 : W := mkw 0x0402100402042650 0x0010084010081099 0x0cfb111c063ffffe 0xbc33ec447018ffff

def z956 : W := mkw 0xfffbddd9b5ba1080 0x23ffef7766d6e842 0xfffffffffffff1ff 0xffffffffffffffc7

def z957 : W := mkw 0xfbf145d1b5aa0000 0x03efc51746d6a800 0xffffffffffff003f 0xfffffffffffffc00

def z958 : W := mkw 0x1124067618cc8b6a 0x04449019d863322d 0x33041ffe39c08ff9 0xc4cc107ff8e7023f

def z959 : W := mkw 0xeedbddd9a5220000 0x23bb6f7766948800 0xccdffffdc6330012 0x73337ffff718cc00

def z960 : W := mkw 0x42c561a2c170d18c 0x110b15868b05c346 0xc3e7e1e3c1fcf1ff 0xff0f9f878f07f3c7

def z961 : W := mkw 0x000422277ccccb6a 0x0c0010889df3332d 0x00000003f9cc8fe0 0x0c0000000fe7323f

def z962 : W := mkw 0xfffbddd924000000 0x23ffef7764900000 0xfffffffffe3f003f 0xfffffffffff8fc00

def z963 : W := mkw 0xfbb0ccd000000000 0x23eec33340000000 0xf304fffc00000011 0x43cc13fff0000000

def z964 : W := mkw 0xfbb00001b5aa0000 0x03eec00006d6a800 0xfff80003ffff0007 0x1bffe0000ffffc00

def z965 : W := mkw 0xfffbddd881200000 0x23ffef7762048000 0xffffffffc7ff003f 0xffffffffff1ffc00

def z966 : W := mkw 0xac06ba036e00ec30 0x0ab01ae80db803b0 0xfc27ff1ffe00fe3f 0xfbf09ffc7ff803f8

def z967 : W := mkw 0xea900001b5aa0000 0x03aa400006d6a800 0xcfd80003ffff002b 0x9f3f60000ffffc00

def z968 : W := mkw 0xfbb04081b5aa0000 0x03eec10206d6a800 0xfffce0e3ffff002f 0xdffff3838ffffc00

def z969 : W := mkw 0xfbb08801b5aa0000 0x03eec22006d6a800 0xfffcee03ffff002f 0xdffff3b80ffffc00

def z970 : W := mkw 0x000422036e00ec30 0x080010880db803b0 0xf007fe03fe00fe37 0xfbc01ff80ff803f8

def z971 : W := mkw 0x04029c5000000000 0x00100a7140000000 0x0007fffc00000010 0x60001ffff0000000

def z972 : W := mkw 0x1124067618cc8b6a 0x04449019d863322d 0x33241ffe39cc0fcd 0x4ccc907ff8e7303f

def z973 : W := mkw 0xa804aa036c00c820 0x0aa012a80db00320 0xf007fe03f800fe37 0xfbc01ff80fe003f8

def z974 : W := mkw 0xfffbddd800000000 0x23ffef7760000000 0xff07fffc00000017 0xe3fc1ffff0000000

def z975 : W := mkw 0xeedbddd800000000 0x23bb6f7760000000 0xc007fffc00000010 0x63001ffff0000000

def z976 : W := mkw 0x57fbddd800000000 0x215fef7760000000 0x0ffffffc0000001e 0xe03ffffff0000000

def z977 : W := mkw 0xffbadcd9b5aa0000 0x23feeb7366d6a800 0xfffcfeffffff002f 0xdffff3fbfffffc00

def z978 : W := mkw 0xfffbddd800101080 0x23ffef7760004042 0xfffffffc003001df 0xe7fffffff000c007

def z979 : W := mkw 0xfffbddd9b5aa0000 0x23ffef7766d6a800 0xfffffffc3fff001f 0xeffffffff0fffc00

def z980 : W := mkw 0x53e945fc91fd13cf 0x154fa517f247f44f 0x03f801fc01ff01c8 0x040fe007f007fc07

def z981 : W := mkw 0x53a044d000000000 0x014e811340000000 0xf324fffc0000001d 0xc3cc93fff0000000

def z982 : W := mkw 0x044b518c021536d1 0x00112d46300854db 0x0cfff1fc063ffffe 0xfc33ffc7f018ffff

def z983 : W := mkw 0x004145d000000000 0x0001051740000000 0x0007fffc00000010 0x60001ffff0000000

def z984 : W := mkw 0x42c561a2c170d18c 0x110b15868b05c346 0xc3c3e1e3c1f0f1ea 0x370f0f878f07c3c7

def z985 : W := mkw 0x1124067618cc8b6a 0x04449019d863322d 0xf3241ffff9cc8fff 0xdfcc907fffe7323f

def z986 : W := mkw 0x57eb55d800000000 0x015fad5760000000 0xfffffffc0000001f 0xe3fffffff0000000

def z987 : W := mkw 0x044bddd800000000 0x20112f7760000000 0x0cfffffc063f003e 0xfc33fffff018fc00

def z988 : W := mkw 0x428460a2c170d18c 0x110a11828b05c346 0xc307e0e3c1f0f1f3 0xf70c1f838f07c3c7

def z989 : W := mkw 0xac16ba036e02ec30 0x0ab05ae80db80bb0 0xfc1ffe03fe03fe37 0xfbf07ff80ff80ff8

def z990 : W := mkw 0xb92422277eccef7a 0x0ee490889dfb33bd 0xff200003ffccffef 0x9ffc80000fff33ff

def z991 : W := mkw 0x00000004021536d1 0x00000000100854db 0x0cf8111c063ffffe 0x9c33e0447018ffff

def z992 : W := mkw 0x46cbddd800000000 0x211b2f7760000000 0xcffffffc0000001f 0xe33ffffff0000000

def z993 : W := mkw 0x0004067608448b6a 0x04001019d821122d 0x33041ffe39c08ffd 0xcccc107ff8e7023f

def z994 : W := mkw 0x000422276e44ef7a 0x0c0010889db913bd 0x00000003fe00ffe0 0x180000000ff803ff

def z995 : W := mkw 0xfffbddd881301084 0x33ffef776204c042 0xfffffffc0030001f 0xe3fffffff000c000

def z996 : W := mkw 0x157bddd800000000 0x2055ef7760000000 0x003ffffc00000010 0x6000fffff0000000

def z997 : W := mkw 0xac1eba0b6e00ec30 0x2ab07ae82db803b0 0xfc1ffe03fe00fe37 0xfbf07ff80ff803f8

def z998 : W := mkw 0xac02ba016e006c30 0x0ab00ae805b801b0 0xfc03fe03fe007e27 0xbbf00ff80ff801f8

def z999 : W := mkw 0xac4bddd800000000 0x22b12f7760000000 0xcc07fffc00000012 0x63301ffff0000000

def z1000 : W := mkw 0x1124067618cc8b6a 0x04449019d863322d 0x33241ffe39cc8fd5 0x48cc907ff8e7323f

def z1001 : W := mkw 0xfffbddd800000000 0x23ffef7760000000 0xf3c7fffc0000001b 0xe3cf1ffff0000000

def z1002 : W := mkw 0xfffbddd800000000 0x23ffef7760000000 0xfffffffc0600003f 0xfbfffffff0180000

def z1003 : W := mkw 0x044b110c021536d1 0x00112c44300854db 0x0cfb101c063fffe6 0x3c33ec407018ffff

def z1004 : W := mkw 0xffe3ddd000000000 0x03ff8f7740000000 0xffe7fffc0000001f 0xe3ff9ffff0000000

def z1005 : W := mkw 0x00042226dbfdffff 0x140010889b6ff7ff 0x00000003ffffffe0 0x1c0000000fffffff

def z1006 : W := mkw 0x00410104001412c0 0x000104041000504b 0x0cfb111c063ffffe 0xbc33ec447018ffff

def z1007 : W := mkw 0xfbb466f3fdeac92e 0x17eed19bcff7ab24 0xf304eee3f9c00001 0x43cc13bb8fe70000

def z1008 : W := mkw 0xfffbddd800000000 0x23ffef7760000000 0xfffffffc0030003f 0xf7fffffff000c000

def z1009 : W := mkw 0x044bddd802113491 0x20112f77600844d2 0x0cdffffc06337012 0x70337ffff018cdc0

def z1010 : W := mkw 0xbd7bddd800000000 0x22f5ef7760000000 0x3cfffffc0000001e 0xe0f3fffff0000000

def z1011 : W := mkw 0xffbadcd800000000 0x23feeb7360000000 0xf304fefc00000001 0x43cc13fbf0000000

def z1012 : W := mkw 0xfffbddd9348a0000 0x23ffef7764d22800 0xfffffffe3fcf003f 0xeffffffff8ff3c00

def z1013 : W := mkw 0x1124247650ccc34a 0x04449091d943330d 0xc327e1ffc1ccf1fb 0xf70c9f87ff0733c7

def z1014 : W := mkw 0xfffbddd9b5aa0000 0x23ffef7766d6a800 0xffffffffffcf001f 0xebffffffffff3c00

def z1015 : W := mkw 0x57fbddd800000000 0x215fef7760000000 0x0307fffc00000010 0x600c1ffff0000000

def z1016 : W := mkw 0xfbf9cdd800000000 0x23efe73760000000 0xf304effc00000001 0x43cc13bff0000000

def z1017 : W := mkw 0x42c145d000000000 0x010b051740000000 0xc3c7fffc0000001b 0xe30f1ffff0000000

def z1018 : W := mkw 0xfffbddd9b5aa0000 0x23ffef7766d6a800 0xfffffffff9ff001f 0xe7ffffffffe7fc00

def z1019 : W := mkw 0xfffbddd802103490 0x23ffef77600840d2 0xfffffffc0630ffff 0xfffffffff018c3ff

def z1020 : W := mkw 0xffbadcd9b5aa0000 0x23feeb7366d6a800 0xff3cfeffffcf0005 0x4bfcf3fbffff3c00

def z1021 : W := mkw 0xac06ba036e00ec30 0x0ab01ae80db803b0 0xfc07fe01fe00fe16 0x7bf01ff807f803f8

def z1022 : W := mkw 0x53f945d800000000 0x214fe51760000000 0xf3fffffc0000001f 0xe3cffffff0000000

def z1023 : W := mkw 0x53f145f491fe13ce 0x154fc517d247f84f 0x03f801fc01ff01c8 0x040fe007f007fc07

def z1024 : W := mkw 0xfbb00001b5aa0000 0x03eec00006d6a800 0x3ff80003ffff002c 0x1cffe0000ffffc00

def z1025 : W := mkw 0x004521224050d188 0x0001148489014346 0xc3c7e1e3c1f0f1fb 0xf70f1f878f07c3c7

def z1026 : W := mkw 0xfbb00001b5aa0000 0x03eec00006d6a800 0xfcf80003ffff0026 0x1ff3e0000ffffc00

def z1027 : W := mkw 0x15229c5000000000 0x00548a7140000000 0x3327fffc0000001d 0xe0cc9ffff0000000

def z1028 : W := mkw 0xffb29c5000000000 0x03feca7140000000 0xfffffffc0000001f 0xe3fffffff0000000

def z1029 : W := mkw 0xac06ba236e40ed38 0x0ab01ae88db903b4 0xff07fee3ffc0fe37 0xfbfc1ffb8fff03f8

def z1030 : W := mkw 0xfffbddd800000000 0x23ffef7760000000 0xfffffffc000081ff 0xe7fffffff0000207

def z1031 : W := mkw 0x1124067618cc8b6a 0x04449019d863322d 0x33271ffe39ccffff 0xfccc9c7ff8e733ff

def z1032 : W := mkw 0xac06ba024800c820 0x02b01ae809200320 0xfc07fe03f800fe37 0xfbf01ff80fe003f8

def z1033 : W := mkw 0xfbb42227ffeeef7a 0x0feed0889fffbbbd 0xfff80003ffffffef 0x9fffe0000fffffff

def z1034 : W := mkw 0x57fbddd800000000 0x215fef7760000000 0xc3fffffc0000001b 0xe30ffffff0000000

def z1035 : W := mkw 0xac06ba036e00ec30 0x0ab01ae80db803b0 0xff07ffe3fe00fe3f 0xfbfc1fff8ff803f8

def z1036 : W := mkw 0xac06ba236e40ed38 0x0ab01ae88db903b4 0xfc07fe03ffc0fff7 0xfff01ff80fff03ff

def z1037 : W := mkw 0x1120067418cc0b6a 0x04448019d063302d 0x33241ffc39cc0fdd 0xcccc907ff0e7303f

def z1038 : W := mkw 0x044b110c021536d1 0x00112c44300854db 0x0cfb111c063fffd6 0x3833ec447018ffff

def z1039 : W := mkw 0xac06ba036e00ec30 0x0ab01ae80db803b0 0xfc07ff03fe00ffff 0xfff01ffc0ff803ff

def z1040 : W := mkw 0x46cbddd800000000 0x211b2f7760000000 0xc307fffc00000011 0x630c1ffff0000000

def z1041 : W := mkw 0xfbb00001b5aa0000 0x03eec00006d6a800 0xffffe003ffff003f 0xffffff800ffffc00

def z1042 : W := mkw 0x46cbddd881200000 0x211b2f7762048000 0xc3c7ffffc1f0003b 0xf70f1fffff07c000

def z1043 : W := mkw 0xea800001a5200000 0x03aa000006948000 0xfff80003ffff002f 0x9fffe0000ffffc00

def z1044 : W := mkw 0x42c161a0c170518c 0x110b05868305c146 0xc3c3e1e3c1f071eb 0xb70f0f878f07c1c7

def z1045 : W := mkw 0x00042022c170d18c 0x100010808b05c346 0xc307e1e3c1f0f1fb 0xf70c1f878f07c3c7

def z1046 : W := mkw 0xfbb00451b5aa0000 0x03eec01146d6a800 0xfffc0ee3ffff002f 0xdffff03b8ffffc00

def z1047 : W := mkw 0xa804aa036e00ec30 0x0aa012a80db803b0 0xf007ee03fe00fe33 0xfbc01fb80ff803f8

def z1048 : W := mkw 0xfbb00001b5aa0000 0x03eec00006d6a800 0xfffc01e3ffff003f 0xdffff0078ffffc00

def z1049 : W := mkw 0xfbb00001b5aa0000 0x03eec00006d6a800 0xfffb0003fffff03f 0xbfffec000fffffc0

def z1050 : W := mkw 0xb9300001b5aa0000 0x02e4c00006d6a800 0x3cf80003ffff002e 0x9cf3e0000ffffc00

def z1051 : W := mkw 0xac069a232e40ad38 0x0ab01a688cb902b4 0x3f041fe23fc08ffd 0xccfc107f88ff023f

def z1052 : W := mkw 0x044b110c021536d1 0x00112c44300854db 0x0ffb111e07ffffff 0xbc3fec44781fffff

def z1053 : W := mkw 0xbd2a9e5d3e8d2e73 0x0ef4aa7974fa34b9 0x3c381e1c3e0f0e04 0x08f0e07870f83c38

def z1054 : W := mkw 0x00042227ffeeef7a 0x0c0010889fffbbbd 0x00000003ffffffe0 0x1c0000000fffffff

def z1055 : W := mkw 0x42c561a2c170d18c 0x110b15868b05c346 0xc3e7f1ffc1f0f1ff 0xf70f9fc7ff07c3c7

def z1056 : W := mkw 0x42c561a2c170d18c 0x110b15868b05c346 0xc307e1e3c1f0f1f1 0x770c1f878f07c3c7

def z1057 : W := mkw 0xfffbddd800000000 0x23ffef7760000000 0xff3ffffc00000015 0x63fcfffff0000000

def z1058 : W := mkw 0xac06ba036e00ec30 0x0ab01ae80db803b0 0xfc07fe03fe3ffe37 0xfff01ff80ff8fff8

def z1059 : W := mkw 0x1124067618cc8b6a 0x04449019d863322d 0x33241ffe39cc8fd9 0x44cc907ff8e7323f

def z1060 : W := mkw 0xbd3adcd800000000 0x22f4eb7360000000 0x3c3cfefc00000004 0x40f0f3fbf0000000

def z1061 : W := mkw 0x000422264854dbee 0x140010889921536f 0x000000000000ffc0 0x00000000000003ff

def z1062 : W := mkw 0xac0eba0b6e00ec30 0x0ab03ae82db803b0 0xfc3ffe1ffe00fe37 0xfbf0fff87ff803f8

def z1063 : W := mkw 0xfffbddd9b7aa2410 0x23ffef7766dea890 0xfffffffffffffe3f 0xfffffffffffffff8

def z1064 : W := mkw 0xbd229c5134880000 0x02f48a7144d22000 0xff27ffffffcc003f 0xfffc9fffffff3000

def z1065 : W := mkw 0xfbf9cdd9b5aa0000 0x23efe73766d6a800 0xf3fceffff9ff0009 0x47cff3bfffe7fc00

def z1066 : W := mkw 0xfffbddd800000000 0x23ffef7760000000 0xfffffffc00008e3f 0xebfffffff0000238

def z1067 : W := mkw 0xfffbddd891aa0000 0x23ffef776246a800 0xfffffffc01c0001f 0xe3fffffff0070000

def z1068 : W := mkw 0x044b110c021536d1 0x00112c44300854db 0x0cfb111c063fffdc 0x2c33ec447018ffff

def z1069 : W := mkw 0xfbb00001b5aa0000 0x03eec00006d6a800 0xfff81003ffff8e3f 0x9fffe0400ffffe38

def z1070 : W := mkw 0x53a0000091a80000 0x014e80000246a000 0xfff80003ffff002f 0x9fffe0000ffffc00

def z1071 : W := mkw 0x156bddd800000000 0x2055af7760000000 0x3ffffffc0000001f 0xe0fffffff0000000

def z1072 : W := mkw 0x044ffbae4a55fffd 0x18113feeb92957ff 0x0007fffc0000ffd0 0x60001ffff00003ff

def z1073 : W := mkw 0x0406ba024a00ec30 0x08101ae8092803b0 0xf007fe03f800fe37 0xfbc01ff80fe003f8

def z1074 : W := mkw 0xfbf9cdd9b5aa0000 0x23efe73766d6a800 0xfffcefffffff002f 0xdffff3bffffffc00

def z1075 : W := mkw 0xfbb00451b5aa0000 0x03eec01146d6a800 0xfff801ffffff002f 0x9fffe007fffffc00

def z1076 : W := mkw 0x044fbf7e4a55fffb 0x0c113efdf92957ff 0x0007fffc0000ffd0 0x60001ffff00003ff

def z1077 : W := mkw 0x044bd98c021536d1 0x20112f66300854db 0x0cfbf11c063ffffe 0xbc33efc47018ffff

def z1078 : W := mkw 0xa80422036c00c820 0x02a010880db00320 0xfc07fe03fe00fe37 0xfbf01ff80ff803f8

def z1079 : W := mkw 0x46cbddd800000000 0x211b2f7760000000 0xc0c7fffc00000012 0x63031ffff0000000

def z1080 : W := mkw 0x1124067618cc8b6a 0x04449019d863322d 0xf327fffe39cc8fff 0xefcc9ffff8e7323f

def z1081 : W := mkw 0xfffbddd800000000 0x23ffef7760000000 0xfffffefc00000007 0x63fffffbf0000000

def z1082 : W := mkw 0xffbadcd800000000 0x23feeb7360000000 0xff3ffefc00000017 0xe3fcfffbf0000000

def z1083 : W := mkw 0x42800001b5aa0000 0x010a000006d6a800 0xcff80003ffff002f 0x9f3fe0000ffffc00

def z1084 : W := mkw 0xfffbddd802002410 0x23ffef7760080090 0xfffffffc06000e1f 0xebfffffff0180038

def z1085 : W := mkw 0xac06ba036e00ec30 0x0ab01ae80db803b0 0xfc3ffe03fe0ffe37 0xfbf0fff80ff83ff8

def z1086 : W := mkw 0x1124267658cccb6a 0x04449099d963332d 0x33241ffff9ccfffd 0xdccc907fffe733ff

def z1087 : W := mkw 0x0004222658dcdbee 0x140010889963736f 0x0000000239ccffe0 0x0c00000008e733ff

def z1088 : W := mkw 0xac4bddd800000000 0x22b12f7760000000 0xf007fffc00000011 0x63c01ffff0000000

def z1089 : W := mkw 0x42c561a2c170d18c 0x110b15868b05c346 0xc3c7e1e3c7fff1fb 0xff0f1f878f1fffc7

def z1090 : W := mkw 0xac06ba036e00ec30 0x0ab01ae80db803b0 0xfc03fe03fe00fe26 0x3bf00ff80ff803f8

def z1091 : W := mkw 0x044bddd800000000 0x20112f7760000000 0x0027fffc0000001c 0xe0009ffff0000000

def z1092 : W := mkw 0x1124067618cc8b6a 0x04449019d863322d 0x3f241ffe3fcc8fff 0xdcfc907ff8ff323f

def z1093 : W := mkw 0x57fbddd891aa0000 0x215fef776246a800 0x03fffffc01ff0018 0x640ffffff007fc00

def z1094 : W := mkw 0xfbb0ccd000000000 0x23eec33340000000 0xfffcfffc0000001f 0xc3fff3fff0000000

def z1095 : W := mkw 0x044b110c021536d1 0x00112c44300854db 0xccfb111fc63fffff 0xbf33ec447f18ffff

def z1096 : W := mkw 0x1124067618cc8b6a 0x04449019d863322d 0x3f3c1ffe3fcf8ffd 0xccfcf07ff8ff3e3f

def z1097 : W := mkw 0x42c561a2c170d18c 0x110b15868b05c346 0xc3c7e1e1c1f0f1da 0x770f1f878707c3c7

def z1098 : W := mkw 0xbd329e553e8e2e72 0x0ef4ca7954fa38b9 0x3c381e1c3e0f0e04 0x08f0e07870f83c38

def z1099 : W := mkw 0xfffbddd9b7bb3491 0x23ffef7766deecd2 0xffffffffffff703f 0xfffffffffffffdc0

def z1100 : W := mkw 0xfffbddd800000000 0x23ffef7760000000 0xf3fffffc00000019 0x63cffffff0000000

def z1101 : W := mkw 0x428460a2c160c10c 0x110a11828b058304 0xc307e1e3c1c0f1fb 0xf70c1f878f0703c7

def z1102 : W := mkw 0xfffbddd800111081 0x23ffef7760004442 0xfffffffc0033001f 0xe3fffffff000cc00

def z1103 : W := mkw 0xbd6b9d5800000000 0x02f5ae7560000000 0xfffffffc0000001f 0xe3fffffff0000000

def z1104 : W := mkw 0xfffbddd800000000 0x23ffef7760000000 0xfffffffc0633001f 0xf3fffffff018cc00

def z1105 : W := mkw 0x044b110c021536d1 0x00112c44300854db 0x0cfb011c063fffea 0x3c33ec047018ffff

def z1106 : W := mkw 0x156bddd800000000 0x2055af7760000000 0x3027fffc00000014 0x60c09ffff0000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z1,z7,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z9,z5,z10]),(0,[z1,z2,z3,z4,z5,z8,z11]),(0,[z1,z12,z2,z3,z4,z5,z8]),(0,[z1,z2,z13,z3,z4,z5,z8])],[(1,[z1,z2,z3,z4,z5,z14]),(0,[z1,z2,z3,z4,z15,z5,z8]),(0,[z16,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z17,z5,z10])],[(0,[z1,z18,z2,z19,z3,z4,z5]),(1,[z1,z2,z20,z4,z5,z8]),(0,[z21,z1,z2,z3,z4,z5,z8])],[(0,[z22,z1,z2,z3,z4,z5,z10]),(0,[z1,z2,z3,z4,z23,z5,z8]),(0,[z24,z1,z18,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z8,z25]),(0,[z1,z2,z3,z4,z26,z5,z8])],[(0,[z1,z2,z27,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z28,z5,z8]),(0,[z29,z1,z2,z3,z4,z5,z8]),(0,[z1,z30,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z10,z31])],[(0,[z1,z32,z2,z3,z4,z5,z10]),(1,[z1,z2,z3,z4,z33,z8]),(0,[z34,z1,z2,z3,z4,z5,z10]),(0,[z1,z35,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z36,z4,z5,z8]),(0,[z37,z24,z1,z2,z3,z4,z8]),(0,[z1,z2,z3,z4,z5,z8,z38]),(0,[z1,z2,z3,z4,z39,z5,z8]),(0,[z1,z18,z2,z3,z4,z5,z40]),(0,[z1,z2,z3,z41,z4,z5,z10])],[(0,[z42,z1,z2,z3,z4,z5,z8]),(0,[z43,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z44,z4,z26,z5,z8]),(0,[z45,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z44,z4,z5,z10]),(0,[z1,z2,z46,z3,z4,z5,z8])]],
   [[(0,[z47,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z48,z4,z5,z8]),(0,[z1,z2,z3,z4,z49,z5,z10]),(0,[z1,z2,z50,z3,z4,z5,z51]),(0,[z1,z2,z3,z52,z4,z53,z8]),(0,[z54,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z8,z55]),(0,[z22,z1,z2,z3,z4,z5,z56]),(0,[z1,z2,z3,z4,z57,z5,z8]),(0,[z1,z2,z3,z58,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z59,z8])],[(0,[z45,z1,z2,z3,z44,z4,z5]),(0,[z1,z2,z3,z4,z60,z5,z8]),(0,[z61,z1,z2,z3,z4,z5,z8]),(0,[z1,z18,z2,z3,z4,z5,z51]),(0,[z1,z2,z62,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z63]),(0,[z1,z2,z3,z64,z4,z5,z8])],[(0,[z65,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z66,z3,z67,z5,z8]),(0,[z68,z1,z2,z3,z4,z5,z10]),(0,[z1,z2,z3,z69,z4,z5,z40])],[(0,[z1,z2,z3,z4,z5,z70,z8]),(0,[z71,z1,z2,z67,z4,z5,z8]),(0,[z72,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z73,z8]),(0,[z1,z2,z3,z4,z74,z5,z8])],[(0,[z1,z2,z3,z4,z5,z75,z8]),(0,[z1,z76,z2,z3,z4,z5,z8]),(0,[z1,z2,z77,z3,z4,z5,z8]),(1,[z1,z2,z66,z67,z5,z8]),(0,[z1,z2,z3,z78,z4,z5,z8]),(0,[z1,z79,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z80,z4,z5,z8]),(0,[z1,z81,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z82,z4,z5,z8])],[(0,[z1,z2,z3,z83,z4,z5,z8]),(0,[z84,z1,z2,z3,z4,z5,z8]),(0,[z1,z85,z2,z3,z4,z5,z86]),(0,[z1,z18,z2,z3,z4,z5,z86]),(0,[z1,z87,z2,z3,z4,z5,z10]),(0,[z1,z2,z3,z88,z4,z5,z8])]],
   [[(0,[z0,z1,z2,z3,z4,z5,z8]),(0,[z89,z1,z2,z3,z4,z5,z8]),(0,[z90,z1,z18,z2,z3,z4,z5]),(0,[z1,z2,z3,z91,z4,z5,z8])],[(0,[z0,z1,z2,z3,z92,z5,z8]),(0,[z1,z2,z3,z4,z93,z5,z8]),(0,[z1,z2,z50,z4,z5,z8,z51])],[(0,[z94,z1,z19,z3,z4,z5,z8]),(0,[z1,z95,z2,z3,z4,z5,z8]),(0,[z96,z1,z2,z3,z4,z5,z8]),(0,[z1,z97,z2,z3,z4,z5,z8]),(0,[z1,z85,z2,z3,z4,z98,z8])],[(0,[z22,z1,z99,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z100,z5,z8]),(0,[z101,z1,z2,z3,z4,z5,z8]),(1,[z102,z1,z2,z4,z5,z8]),(0,[z103,z1,z2,z3,z4,z5,z10]),(0,[z1,z104,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z105,z5,z8]),(0,[z1,z2,z3,z106,z4,z5,z10])],[(0,[z1,z2,z3,z4,z5,z107,z8]),(0,[z1,z108,z2,z3,z4,z5,z8]),(0,[z109,z1,z2,z3,z4,z5,z8])],[(0,[z110,z1,z2,z3,z111,z5,z8]),(0,[z1,z2,z3,z4,z5,z112,z8]),(0,[z71,z1,z2,z3,z113,z5,z8]),(0,[z1,z2,z3,z114,z4,z5,z8]),(0,[z115,z1,z85,z2,z3,z4,z5]),(0,[z1,z2,z3,z116,z4,z5,z8])],[(0,[z71,z1,z2,z3,z4,z5,z10]),(0,[z1,z87,z2,z3,z117,z5,z8]),(0,[z118,z1,z18,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z8,z119]),(0,[z1,z2,z3,z120,z4,z5,z8])],[(0,[z1,z2,z121,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z122]),(0,[z1,z2,z3,z67,z123,z5,z8]),(0,[z1,z2,z124,z3,z4,z5,z8]),(0,[z125,z1,z2,z3,z4,z5,z8])]],
   [[(0,[z1,z2,z3,z4,z126,z5,z8]),(0,[z1,z2,z3,z4,z86,z127,z8]),(0,[z128,z1,z2,z3,z4,z5,z8]),(0,[z129,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z130,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z131,z8]),(0,[z132,z1,z2,z3,z52,z5,z8])],[(0,[z133,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z134,z8]),(0,[z135,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z136,z3,z4,z49,z8]),(0,[z1,z2,z137,z3,z4,z5,z8]),(0,[z1,z2,z3,z52,z4,z5,z138])],[(0,[z139,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z140,z5,z8]),(0,[z141,z1,z2,z3,z4,z5,z10])],[(0,[z1,z2,z3,z4,z142,z5,z8]),(0,[z1,z2,z3,z143,z4,z5,z8])],[(0,[z144,z1,z2,z3,z4,z5,z8]),(0,[z103,z141,z1,z2,z3,z4,z5]),(0,[z1,z2,z136,z3,z4,z5,z8])],[(0,[z145,z1,z2,z3,z4,z5,z8]),(1,[z1,z146,z147,z4,z5,z8]),(0,[z1,z2,z3,z117,z26,z5,z8]),(0,[z1,z2,z3,z148,z4,z5,z8]),(0,[z1,z2,z3,z106,z4,z149,z5]),(0,[z1,z2,z3,z150,z4,z5,z8])],[(0,[z1,z99,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z151,z8]),(0,[z29,z1,z152,z3,z4,z5,z8]),(0,[z1,z2,z3,z153,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z10,z154])],[(0,[z1,z2,z155,z3,z4,z5,z8]),(0,[z156,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z157,z8])]],
   [[(0,[z1,z2,z158,z3,z4,z5,z8]),(0,[z1,z3,z4,z9,z5,z8,z159]),(0,[z1,z2,z3,z4,z160,z5,z8]),(0,[z1,z2,z3,z4,z161,z5,z8]),(0,[z1,z162,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z10,z63])],[(0,[z1,z3,z44,z4,z117,z5,z8]),(0,[z1,z2,z163,z3,z4,z5,z8]),(0,[z1,z85,z2,z3,z4,z9,z5]),(0,[z1,z164,z2,z3,z4,z5,z8]),(0,[z1,z18,z2,z3,z4,z9,z5]),(0,[z165,z1,z2,z3,z4,z5,z10]),(1,[z1,z2,z3,z4,z5,z10])],[(0,[z110,z1,z18,z2,z3,z4,z5]),(0,[z166,z1,z2,z3,z4,z5,z8]),(0,[z167,z1,z2,z168,z4,z5,z8]),(0,[z1,z2,z169,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z170,z5,z10])],[(0,[z94,z1,z99,z3,z4,z5,z8]),(0,[z171,z1,z2,z172,z4,z5,z8]),(0,[z1,z2,z3,z4,z173,z5,z8]),(0,[z1,z2,z3,z174,z4,z5,z8]),(0,[z115,z1,z2,z3,z4,z175,z5]),(0,[z1,z176,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z177,z5,z8])],[(0,[z1,z2,z3,z178,z4,z5,z8]),(0,[z179,z1,z2,z3,z4,z5,z8]),(1,[z1,z85,z3,z4,z5,z159]),(0,[z103,z115,z1,z2,z3,z4,z5]),(0,[z1,z2,z66,z3,z26,z5,z8]),(0,[z180,z1,z2,z3,z4,z5,z8]),(0,[z115,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z181,z8]),(0,[z182,z1,z2,z3,z4,z5,z183]),(1,[z110,z2,z3,z111,z5,z8]),(0,[z184,z1,z2,z3,z4,z5,z8]),(0,[z0,z1,z2,z185,z4,z5,z8]),(0,[z1,z2,z186,z3,z4,z5,z8])],[],[(1,[z1,z2,z3,z4,z5,z56]),(0,[z1,z2,z3,z4,z5,z8,z183]),(0,[z187,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z188,z8]),(0,[z189,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z190,z5,z8]),(0,[z1,z2,z3,z4,z191,z5,z8]),(0,[z1,z2,z3,z4,z5,z10,z159]),(0,[z1,z2,z3,z4,z5,z192,z10]),(0,[z141,z1,z2,z3,z143,z4,z5]),(0,[z193,z1,z2,z3,z4,z5,z10])]],
   [[(0,[z1,z32,z2,z3,z4,z5,z14]),(0,[z1,z2,z194,z3,z4,z5,z8]),(0,[z195,z1,z2,z3,z4,z5,z10])],[(0,[z29,z1,z87,z2,z3,z5,z8]),(0,[z1,z2,z3,z4,z196,z5,z8]),(0,[z197,z1,z2,z3,z4,z5,z8]),(0,[z1,z18,z2,z3,z52,z4,z5])],[(0,[z198,z1,z2,z3,z4,z5,z10]),(1,[z1,z2,z168,z4,z5,z8]),(0,[z1,z2,z199,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z200,z8]),(0,[z1,z18,z2,z3,z4,z5,z201]),(1,[z1,z2,z3,z4,z149,z5])],[(0,[z1,z2,z19,z3,z4,z5,z10]),(0,[z202,z1,z2,z3,z4,z5,z8]),(0,[z203,z1,z2,z3,z4,z5,z8]),(1,[z198,z2,z3,z4,z5,z204]),(0,[z1,z2,z3,z205,z4,z5,z8]),(0,[z206,z1,z2,z3,z4,z5,z8]),(0,[z68,z1,z2,z136,z4,z5,z8]),(0,[z1,z2,z136,z3,z4,z105,z5])],[(0,[z207,z1,z2,z3,z4,z5,z8]),(0,[z166,z1,z18,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z117,z5,z8]),(0,[z1,z2,z3,z4,z208,z5,z8])],[(0,[z209,z1,z2,z3,z4,z5,z8]),(0,[z210,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z211,z4,z5,z8])]],
   [[(0,[z1,z2,z3,z4,z212,z5,z8]),(1,[z128,z1,z2,z3,z5,z8]),(0,[z1,z2,z50,z3,z4,z175,z5]),(0,[z1,z2,z213,z3,z4,z5,z10])],[(0,[z1,z2,z3,z4,z214,z5,z8]),(0,[z0,z1,z2,z3,z4,z215,z8]),(0,[z71,z1,z2,z3,z216,z5,z8]),(0,[z1,z2,z3,z4,z5,z217,z8])],[(0,[z218,z1,z2,z3,z4,z5,z8]),(0,[z219,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z147,z3,z4,z5,z10]),(0,[z1,z18,z2,z3,z4,z5,z192])],[(0,[z68,z1,z2,z172,z4,z5,z8]),(0,[z220,z1,z2,z3,z4,z5,z8]),(0,[z71,z1,z3,z44,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z53,z10]),(0,[z1,z2,z3,z4,z5,z10,z10])],[(0,[z221,z1,z2,z3,z4,z5,z8]),(0,[z222,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z223,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z201,z8,z10]),(0,[z1,z18,z224,z2,z3,z4,z5])],[(0,[z166,z1,z2,z3,z4,z5,z204]),(0,[z1,z2,z3,z4,z225,z5,z8]),(0,[z226,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z227,z4,z5,z8]),(0,[z228,z1,z2,z3,z4,z117,z5]),(0,[z1,z2,z3,z4,z229,z5,z8]),(0,[z1,z18,z2,z136,z3,z4,z5])],[(0,[z132,z1,z2,z3,z230,z5,z8]),(0,[z1,z2,z3,z231,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z232,z8]),(0,[z233,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z234,z4,z5,z8]),(0,[z1,z235,z2,z3,z4,z5,z8])]],
   [[(0,[z1,z236,z2,z3,z4,z5,z8]),(0,[z237,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z238,z4,z5,z8]),(0,[z1,z2,z3,z239,z4,z5,z8])],[(0,[z1,z2,z240,z3,z4,z5,z8]),(0,[z1,z2,z3,z241,z4,z5,z8]),(0,[z1,z2,z3,z143,z4,z5,z86]),(0,[z1,z2,z3,z4,z175,z5,z10])],[(0,[z1,z2,z3,z242,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z243,z8]),(0,[z1,z2,z3,z4,z244,z5,z8])],[(0,[z245,z1,z2,z3,z4,z5,z8]),(0,[z246,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z215,z10]),(0,[z24,z1,z2,z3,z4,z5,z10]),(0,[z1,z2,z247,z3,z4,z5,z8])],[(0,[z1,z18,z2,z172,z3,z4,z5]),(0,[z1,z2,z3,z248,z4,z5,z8]),(0,[z1,z2,z66,z67,z4,z5,z8]),(0,[z249,z1,z2,z3,z4,z5,z8])],[(0,[z24,z1,z2,z3,z4,z8,z10]),(0,[z1,z2,z3,z4,z250,z5,z8]),(1,[z1,z251,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z252]),(0,[z115,z1,z2,z3,z4,z5,z51]),(0,[z253,z1,z2,z3,z4,z5,z8]),(0,[z1,z18,z18,z2,z3,z4,z5])],[]],
   [[(0,[z1,z2,z3,z254,z4,z5,z8]),(0,[z1,z2,z3,z4,z255,z5,z8]),(0,[z1,z2,z3,z4,z256,z5,z8])],[(0,[z166,z1,z2,z3,z4,z5,z86]),(0,[z1,z2,z3,z4,z216,z5,z8]),(0,[z1,z18,z2,z3,z143,z4,z5])],[(0,[z257,z1,z2,z3,z4,z5,z8])],[(0,[z182,z1,z2,z172,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z258,z8]),(0,[z1,z146,z2,z67,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z259,z8]),(0,[z1,z2,z3,z4,z5,z8,z260]),(0,[z1,z2,z3,z261,z4,z5,z8]),(0,[z1,z2,z262,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z263,z8]),(1,[z65,z1,z2,z3,z4,z8])],[(0,[z22,z1,z19,z3,z4,z5,z8]),(0,[z264,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z204,z51]),(0,[z1,z2,z265,z3,z4,z5,z8]),(0,[z1,z2,z3,z266,z4,z5,z8])],[(0,[z1,z2,z3,z267,z4,z5,z8]),(0,[z268,z1,z2,z3,z4,z5,z8]),(0,[z1,z85,z2,z3,z4,z5,z204]),(0,[z1,z18,z2,z3,z4,z5,z204]),(0,[z269,z1,z2,z3,z4,z5,z8]),(0,[z115,z1,z2,z50,z4,z5,z8]),(0,[z1,z270,z2,z3,z4,z5,z10]),(1,[z1,z18,z2,z3,z4,z10])],[(0,[z1,z1,z2,z3,z4,z5,z8]),(0,[z182,z1,z2,z254,z4,z5,z8]),(0,[z271,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z272,z8]),(0,[z1,z2,z66,z3,z4,z5,z10])]],
   [[(0,[z273,z1,z2,z3,z4,z5,z8]),(0,[z1,z18,z2,z3,z230,z4,z5]),(0,[z1,z274,z2,z3,z4,z5,z8]),(0,[z275,z1,z2,z3,z4,z5,z8]),(0,[z198,z2,z3,z4,z5,z8,z204]),(0,[z1,z2,z3,z4,z276,z5,z8])],[(0,[z94,z1,z2,z3,z4,z5,z8]),(0,[z277,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z278]),(0,[z1,z2,z3,z4,z5,z279,z8]),(0,[z1,z2,z3,z280,z4,z5,z8]),(0,[z103,z1,z2,z3,z4,z5,z159]),(0,[z115,z1,z2,z4,z175,z5,z8]),(1,[z37,z1,z18,z2,z3,z4])],[(0,[z1,z2,z281,z3,z4,z5,z8]),(0,[z0,z1,z121,z3,z4,z5,z8]),(0,[z1,z18,z2,z3,z4,z117,z5]),(0,[z282,z1,z2,z3,z4,z5,z8]),(0,[z283,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z136,z3,z4,z5,z284])],[(0,[z285,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z286,z3,z4,z5,z8]),(0,[z1,z2,z3,z123,z26,z5,z8]),(1,[z118,z1,z3,z4,z287,z8]),(1,[z1,z2,z3,z288,z4,z5]),(0,[z289,z1,z2,z3,z4,z5,z8])],[(0,[z290,z1,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z291,z5,z8]),(0,[z1,z146,z2,z3,z4,z5,z10]),(1,[z132,z1,z2,z3,z106,z8]),(0,[z1,z2,z3,z4,z292,z5,z10])],[(0,[z1,z2,z3,z67,z4,z5,z10]),(0,[z1,z2,z3,z293,z4,z5,z8]),(1,[z1,z2,z136,z4,z192,z8])],[(1,[z94,z19,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z294,z5,z8]),(0,[z167,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z295,z5,z8]),(0,[z118,z1,z2,z3,z4,z5,z10]),(0,[z29,z1,z2,z3,z67,z5,z8]),(0,[z1,z2,z3,z4,z5,z296,z8]),(0,[z1,z2,z3,z4,z292,z8,z10])]],
   [[(0,[z1,z2,z3,z4,z297,z5,z8]),(0,[z1,z2,z3,z298,z4,z5,z8]),(0,[z1,z2,z3,z299,z4,z5,z8]),(0,[z1,z2,z3,z4,z300,z5,z8]),(1,[z115,z1,z2,z4,z175,z5])],[(0,[z182,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z5,z8]),(0,[z1,z2,z3,z4,z5,z301,z8]),(0,[z1,z2,z3,z4,z302,z5,z8]),(0,[z167,z1,z87,z3,z4,z5,z8]),(0,[z1,z152,z2,z3,z4,z5,z8])],[(0,[z1,z303,z2,z3,z4,z5,z8]),(0,[z1,z3,z123,z4,z117,z5,z8]),(0,[z1,z2,z3,z304,z4,z5,z8]),(0,[z1,z2,z3,z4,z305,z5,z8]),(0,[z29,z1,z18,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z306,z5,z8])],[(0,[z22,z99,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z8])],[(0,[z1,z2,z3,z4,z307,z5,z8]),(0,[z1,z2,z3,z4,z5,z308,z8])],[(0,[z182,z1,z2,z3,z4,z5,z309]),(0,[z1,z2,z3,z67,z117,z5,z8])],[(0,[z1,z2,z3,z4,z310,z5,z8]),(0,[z1,z2,z3,z106,z5,z53,z8]),(0,[z1,z2,z311,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z10,z312])],[(0,[z1,z2,z3,z230,z4,z5,z10]),(0,[z0,z24,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z23,z5,z313]),(0,[z1,z2,z3,z314,z4,z5,z8]),(0,[z1,z315,z2,z3,z4,z5,z8]),(0,[z316,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z317,z5,z8]),(0,[z1,z2,z3,z4,z5,z318,z8])]],
   [[(0,[z1,z2,z319,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z86,z10]),(0,[z102,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z320,z5,z8]),(0,[z1,z2,z3,z321,z4,z5,z8]),(0,[z1,z2,z322,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z201,z8]),(0,[z118,z1,z3,z4,z287,z5,z8]),(0,[z132,z1,z2,z3,z106,z5,z8])],[(0,[z1,z2,z3,z4,z5,z127,z8]),(0,[z1,z147,z3,z44,z4,z5,z8])],[(1,[z1,z2,z3,z4,z5,z309]),(0,[z110,z1,z2,z3,z4,z5,z10]),(0,[z1,z2,z3,z323,z4,z5,z8]),(0,[z1,z85,z2,z3,z4,z33,z8]),(0,[z324,z1,z2,z3,z4,z5,z8]),(0,[z132,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z172,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z325,z5,z8]),(0,[z1,z2,z3,z4,z326,z5,z8]),(0,[z128,z1,z2,z3,z44,z5,z8]),(0,[z327,z1,z2,z3,z4,z5,z8])],[(0,[z328,z1,z2,z3,z4,z5,z8]),(1,[z1,z329,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z330,z8]),(0,[z331,z1,z2,z3,z4,z5,z8]),(0,[z84,z1,z18,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z332,z8]),(0,[z0,z1,z18,z2,z3,z4,z5]),(0,[z166,z198,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z333]),(0,[z334,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z335,z5,z8])],[(1,[z0,z2,z3,z4,z215,z8]),(0,[z167,z29,z1,z2,z3,z5,z8])]],
   [[(1,[z1,z2,z3,z4,z127,z8]),(1,[z71,z1,z44,z4,z5,z8]),(0,[z1,z2,z3,z4,z336,z5,z8])],[(0,[z1,z2,z3,z337,z4,z5,z8]),(0,[z1,z2,z3,z338,z4,z5,z8]),(0,[z1,z2,z3,z4,z339,z5,z8]),(0,[z1,z2,z340,z3,z4,z5,z8]),(0,[z37,z1,z2,z3,z4,z292,z8])],[(0,[z1,z2,z341,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z342,z5,z8]),(0,[z1,z3,z4,z287,z5,z201,z8]),(0,[z343,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z344,z8]),(0,[z103,z1,z2,z3,z69,z4,z5])],[(0,[z1,z2,z3,z4,z345,z5,z8]),(0,[z346,z1,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z347,z4,z5]),(0,[z1,z2,z147,z4,z26,z5,z8]),(0,[z1,z2,z348,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z349,z5,z8])],[(1,[z1,z32,z3,z4,z201,z8]),(0,[z1,z2,z3,z350,z4,z5,z8]),(0,[z1,z2,z3,z4,z351,z5,z8]),(0,[z1,z2,z3,z4,z5,z352,z8]),(0,[z1,z2,z3,z4,z5,z353,z10])],[(0,[z1,z2,z3,z354,z4,z5,z8]),(0,[z1,z2,z3,z355,z4,z5,z8])],[(0,[z356,z1,z2,z3,z4,z5,z8]),(0,[z1,z357,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z111,z5,z10]),(0,[z1,z2,z3,z4,z5,z8,z358]),(0,[z1,z2,z3,z4,z5,z359,z8]),(0,[z1,z2,z3,z4,z5,z8,z360]),(0,[z1,z2,z3,z4,z5,z361,z8]),(1,[z1,z2,z3,z4,z105,z5]),(0,[z1,z2,z3,z362,z4,z5,z10])]],
   [[(1,[z166,z2,z3,z4,z5,z86]),(0,[z363,z1,z2,z3,z4,z5,z8]),(0,[z29,z1,z2,z3,z26,z5,z8]),(0,[z1,z2,z3,z4,z5,z364,z8]),(0,[z141,z1,z2,z3,z143,z5,z8])],[(0,[z1,z18,z99,z2,z3,z4,z5]),(0,[z365,z1,z2,z3,z4,z5,z8]),(0,[z0,z1,z274,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z366,z8]),(0,[z166,z2,z3,z4,z5,z86,z8]),(0,[z1,z367,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z368,z5,z8])],[(0,[z171,z1,z2,z254,z4,z5,z8]),(0,[z1,z2,z369,z3,z4,z5,z8]),(0,[z1,z2,z370,z3,z4,z5,z8]),(0,[z1,z18,z2,z3,z106,z4,z5])],[(0,[z1,z85,z2,z3,z4,z5,z159]),(0,[z1,z18,z2,z3,z4,z5,z159]),(0,[z1,z2,z136,z3,z4,z192,z8]),(0,[z1,z371,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z372,z4,z5,z8]),(0,[z1,z2,z3,z4,z373,z5,z8]),(0,[z103,z1,z3,z4,z9,z5,z8])],[(0,[z1,z19,z3,z4,z5,z201,z8]),(0,[z110,z2,z3,z4,z111,z5,z8]),(1,[z24,z1,z2,z3,z4,z10]),(0,[z1,z2,z3,z4,z5,z374,z8]),(0,[z1,z2,z3,z4,z287,z5,z8]),(0,[z1,z2,z3,z375,z4,z5,z8]),(0,[z376,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z51])],[(0,[z377,z1,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z183]),(0,[z1,z378,z2,z3,z4,z5,z8]),(0,[z1,z2,z379,z3,z4,z5,z8]),(0,[z380,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z172,z4,z5,z192,z8]),(0,[z0,z1,z2,z3,z4,z5,z381]),(0,[z1,z2,z3,z4,z382,z5,z8]),(0,[z1,z87,z3,z44,z4,z5,z8]),(0,[z1,z2,z3,z123,z4,z5,z10]),(0,[z29,z1,z2,z66,z4,z5,z8]),(0,[z1,z2,z3,z4,z383,z5,z8]),(1,[z1,z2,z3,z52,z53,z8])]],
   [[(0,[z384,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z385,z5,z8])],[(0,[z1,z2,z3,z4,z5,z8,z386]),(0,[z24,z2,z3,z4,z23,z5,z8]),(0,[z1,z2,z3,z143,z4,z5,z204])],[(0,[z1,z2,z3,z113,z4,z5,z8]),(0,[z1,z2,z387,z3,z4,z5,z8]),(0,[z1,z2,z136,z4,z5,z192,z8]),(0,[z115,z1,z18,z2,z3,z4,z5]),(1,[z141,z1,z2,z3,z143,z5]),(0,[z1,z2,z3,z4,z5,z388,z8])],[(1,[z22,z99,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z389,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z390]),(0,[z1,z2,z3,z391,z4,z5,z8])],[(0,[z1,z2,z392,z3,z4,z5,z8]),(0,[z171,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z309,z8]),(0,[z1,z2,z3,z4,z5,z8,z393]),(0,[z1,z2,z3,z4,z394,z5,z8])],[(0,[z1,z2,z3,z4,z395,z5,z8]),(0,[z1,z2,z396,z3,z4,z5,z8]),(0,[z397,z1,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z386]),(0,[z1,z2,z50,z3,z4,z5,z10])],[(0,[z1,z2,z3,z4,z5,z8,z398]),(0,[z1,z2,z3,z399,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z400]),(0,[z1,z2,z3,z4,z401,z5,z8]),(0,[z1,z2,z3,z402,z4,z5,z8])],[(1,[z1,z2,z3,z4,z5,z332]),(0,[z1,z2,z4,z403,z117,z5,z8]),(1,[z1,z2,z3,z4,z5,z390]),(0,[z1,z85,z2,z3,z4,z5,z10]),(0,[z1,z2,z3,z52,z4,z5,z10]),(0,[z37,z1,z2,z3,z4,z5,z8]),(0,[z1,z18,z2,z3,z4,z5,z10])]],
   [[(0,[z404,z1,z2,z3,z4,z5,z10]),(0,[z0,z1,z2,z20,z4,z5,z8]),(0,[z68,z1,z2,z4,z49,z5,z8]),(0,[z1,z2,z3,z405,z4,z5,z8]),(0,[z1,z18,z2,z3,z4,z5,z53]),(0,[z1,z2,z3,z406,z4,z5,z8])],[(0,[z407,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z9,z5,z8]),(0,[z1,z18,z2,z3,z4,z8,z10])],[(0,[z408,z1,z2,z3,z4,z5,z8]),(0,[z68,z1,z2,z254,z4,z5,z8]),(0,[z404,z2,z3,z230,z4,z5,z8]),(0,[z409,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z410,z5,z8]),(0,[z411,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z17,z5,z8])],[(0,[z1,z2,z4,z49,z5,z192,z8]),(0,[z207,z1,z18,z2,z3,z4,z5])],[(0,[z22,z1,z2,z3,z4,z5,z8]),(0,[z1,z18,z2,z3,z254,z4,z5]),(0,[z412,z1,z2,z3,z4,z5,z8]),(0,[z1,z18,z2,z3,z4,z5,z215]),(0,[z24,z1,z2,z3,z4,z23,z8]),(1,[z1,z2,z3,z4,z295,z5]),(0,[z1,z2,z3,z4,z413,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z138]),(0,[z1,z2,z3,z69,z4,z5,z10])],[(0,[z1,z2,z414,z3,z4,z5,z8]),(0,[z1,z2,z415,z3,z4,z5,z8]),(0,[z71,z29,z1,z2,z4,z5,z8]),(0,[z1,z2,z3,z4,z416,z5,z8]),(0,[z417,z1,z2,z3,z4,z5,z8])],[(0,[z34,z1,z2,z3,z4,z5,z8]),(0,[z404,z110,z2,z3,z4,z5,z8]),(0,[z0,z2,z3,z4,z5,z215,z8]),(0,[z418,z1,z2,z3,z4,z5,z8]),(0,[z1,z32,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z419,z4,z5,z8]),(0,[z1,z2,z3,z420,z4,z5,z8])],[(0,[z1,z2,z421,z3,z4,z5,z8]),(0,[z1,z422,z2,z3,z4,z5,z8]),(0,[z37,z1,z2,z3,z4,z201,z8]),(0,[z1,z2,z3,z41,z4,z5,z8])]],
   [[(0,[z1,z2,z3,z44,z4,z5,z8]),(0,[z1,z2,z3,z423,z4,z5,z8]),(0,[z1,z2,z251,z3,z4,z5,z8]),(0,[z1,z2,z3,z424,z4,z5,z8])],[(0,[z1,z2,z3,z4,z49,z5,z8]),(0,[z68,z1,z2,z3,z4,z49,z8]),(0,[z1,z2,z3,z4,z5,z425,z8])],[(0,[z426,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z284])],[(0,[z427,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z428,z4,z5,z8]),(0,[z429,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z430]),(0,[z1,z2,z3,z4,z431,z5,z8])],[(0,[z1,z2,z3,z432,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z204,z40]),(0,[z141,z1,z85,z2,z3,z4,z5]),(0,[z68,z1,z2,z3,z4,z5,z8]),(0,[z1,z18,z2,z3,z69,z4,z5])],[(0,[z433,z1,z2,z3,z4,z5,z8]),(0,[z2,z3,z4,z23,z5,z215,z8]),(0,[z434,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z435,z8])],[(0,[z1,z2,z185,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z6]),(0,[z1,z32,z2,z3,z4,z201,z8]),(0,[z1,z18,z2,z3,z4,z26,z5])],[(0,[z22,z1,z18,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z436,z5,z8]),(0,[z437,z1,z2,z3,z4,z5,z8])]],
   [[(0,[z1,z2,z3,z4,z5,z8,z438]),(0,[z1,z87,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z439,z4,z5,z8])],[(0,[z171,z2,z172,z3,z4,z5,z8]),(0,[z1,z2,z440,z3,z4,z5,z8]),(0,[z441,z1,z2,z3,z4,z5,z8]),(0,[z1,z18,z2,z442,z3,z4,z5])],[(0,[z404,z1,z2,z3,z230,z5,z8]),(1,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z23,z5,z10]),(0,[z443,z1,z2,z3,z4,z5,z8]),(0,[z1,z444,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z445,z8]),(0,[z1,z2,z3,z4,z26,z5,z10])],[(0,[z94,z22,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z446]),(0,[z65,z1,z2,z3,z4,z86,z8]),(0,[z1,z2,z3,z4,z447,z5,z8]),(0,[z29,z1,z2,z3,z4,z5,z10]),(0,[z1,z2,z3,z448,z4,z5,z8])],[(0,[z1,z2,z3,z449,z4,z5,z8]),(0,[z1,z2,z3,z106,z4,z5,z8])],[(0,[z450,z1,z2,z3,z4,z5,z8]),(0,[z182,z2,z3,z254,z4,z5,z8]),(0,[z1,z2,z451,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z452,z8]),(0,[z1,z2,z3,z4,z287,z5,z390]),(0,[z1,z2,z3,z288,z4,z49,z5])],[(0,[z1,z2,z3,z4,z5,z8,z453]),(0,[z1,z2,z3,z4,z454,z5,z8]),(0,[z455,z1,z2,z3,z4,z5,z8]),(0,[z1,z456,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z457,z5,z8]),(0,[z71,z1,z2,z3,z4,z5,z8]),(0,[z103,z1,z2,z50,z3,z4,z5]),(0,[z1,z2,z458,z3,z4,z5,z8])]],
   [[(0,[z1,z2,z3,z459,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z460,z8]),(0,[z461,z1,z2,z3,z4,z5,z8]),(0,[z68,z1,z2,z3,z4,z192,z8]),(0,[z1,z2,z442,z3,z4,z5,z8])],[(0,[z118,z1,z19,z3,z4,z5,z8]),(0,[z462,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z463,z3,z4,z5,z8]),(0,[z1,z18,z87,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z464,z8])],[(0,[z465,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z466,z5,z8])],[(0,[z1,z2,z3,z467,z4,z5,z8]),(0,[z468,z1,z2,z3,z4,z5,z8]),(0,[z469,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z470,z3,z4,z5,z8]),(0,[z141,z1,z2,z3,z4,z5,z8])],[(0,[z1,z471,z2,z3,z4,z5,z8]),(0,[z0,z1,z2,z3,z4,z23,z8]),(0,[z1,z87,z3,z123,z4,z5,z8]),(0,[z37,z1,z2,z3,z4,z287,z8]),(0,[z472,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z473,z5,z8]),(0,[z1,z146,z147,z3,z4,z5,z8]),(0,[z1,z18,z32,z2,z3,z4,z5])],[(0,[z1,z18,z2,z3,z4,z111,z5])],[(0,[z94,z1,z18,z2,z3,z4,z5]),(0,[z1,z2,z3,z474,z4,z5,z8]),(0,[z0,z1,z2,z3,z4,z5,z10]),(0,[z475,z1,z2,z3,z4,z5,z8]),(0,[z476,z1,z2,z3,z4,z5,z8]),(0,[z477,z1,z2,z3,z4,z5,z8])]],
   [[(0,[z478,z1,z2,z3,z4,z5,z8]),(0,[z228,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z479,z8])],[(0,[z480,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z481]),(0,[z0,z1,z2,z3,z4,z8,z10]),(0,[z482,z1,z2,z3,z4,z5,z8]),(0,[z167,z1,z2,z66,z3,z5,z8]),(0,[z1,z2,z3,z4,z5,z483,z8]),(0,[z484,z1,z2,z3,z4,z5,z8]),(0,[z485,z1,z2,z3,z4,z5,z8])],[(1,[z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z486,z5,z8]),(0,[z165,z1,z2,z3,z4,z5,z8])],[(0,[z1,z99,z3,z4,z5,z201,z8]),(1,[z1,z2,z3,z92,z5,z8]),(0,[z1,z2,z3,z487,z4,z5,z8]),(0,[z1,z32,z2,z3,z4,z287,z8]),(0,[z1,z2,z3,z4,z170,z5,z8]),(0,[z1,z224,z2,z3,z4,z5,z8])],[(0,[z488,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z489,z5,z8]),(0,[z132,z1,z2,z3,z111,z5,z8]),(0,[z1,z2,z3,z4,z490,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z491]),(0,[z1,z2,z492,z3,z4,z5,z8]),(0,[z1,z2,z493,z3,z4,z5,z8]),(0,[z1,z18,z494,z2,z3,z4,z5])],[(0,[z1,z2,z3,z495,z4,z5,z8]),(0,[z1,z18,z2,z3,z4,z23,z5]),(0,[z167,z1,z18,z2,z3,z4,z5]),(0,[z1,z2,z3,z496,z4,z5,z8])],[(0,[z1,z2,z3,z497,z4,z5,z8]),(0,[z1,z2,z3,z498,z4,z5,z8]),(0,[z499,z1,z2,z3,z4,z5,z8]),(0,[z125,z1,z2,z3,z4,z5,z10])],[(0,[z182,z1,z18,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z4,z5,z8]),(0,[z167,z1,z2,z3,z123,z5,z8]),(0,[z1,z2,z500,z3,z4,z5,z8]),(0,[z1,z501,z2,z3,z4,z5,z8])]],
   [[(0,[z2,z172,z3,z254,z4,z5,z8]),(0,[z167,z1,z3,z4,z117,z5,z8]),(0,[z1,z2,z3,z502,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z192,z8]),(0,[z193,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z503,z3,z4,z5,z8]),(0,[z504,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z505,z4,z5,z8]),(0,[z1,z2,z254,z4,z5,z192,z8]),(0,[z195,z1,z2,z3,z4,z5,z8])],[(0,[z118,z1,z99,z3,z4,z5,z8]),(0,[z1,z329,z2,z3,z4,z23,z5]),(0,[z506,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z500,z3,z4,z287,z5]),(0,[z1,z2,z3,z4,z5,z507,z8]),(0,[z1,z2,z3,z143,z4,z5,z10])],[(0,[z1,z508,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z509,z4,z5,z8]),(0,[z198,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z510,z8]),(0,[z511,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z136,z3,z4,z5,z10])],[(0,[z512,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z19,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z513,z5,z8]),(0,[z1,z99,z2,z3,z4,z5,z10]),(0,[z1,z2,z3,z338,z44,z5,z8]),(0,[z1,z2,z3,z4,z514,z5,z8]),(0,[z515,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z516,z5,z8]),(0,[z1,z2,z4,z175,z5,z8,z51]),(1,[z1,z18,z2,z3,z4,z5])],[(0,[z1,z2,z517,z3,z4,z5,z8])],[(0,[z1,z2,z168,z3,z4,z5,z8])]],
   [[(0,[z1,z518,z2,z3,z4,z5,z8]),(1,[z24,z2,z3,z4,z23,z8]),(0,[z1,z2,z519,z3,z4,z5,z8]),(0,[z1,z2,z3,z520,z4,z5,z8]),(0,[z29,z1,z251,z3,z4,z5,z8]),(0,[z1,z18,z2,z3,z439,z4,z5])],[(0,[z1,z2,z3,z521,z4,z5,z8]),(0,[z1,z2,z3,z4,z522,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z204]),(0,[z166,z1,z2,z3,z4,z5,z10]),(0,[z523,z1,z2,z3,z4,z5,z8]),(0,[z29,z1,z146,z2,z4,z5,z8]),(1,[z1,z87,z3,z123,z5,z8]),(0,[z1,z2,z3,z4,z5,z524,z8]),(1,[z29,z1,z2,z26,z5,z8]),(0,[z132,z1,z18,z2,z3,z4,z5]),(0,[z525,z1,z2,z3,z4,z5,z8]),(0,[z141,z1,z2,z3,z4,z5,z40]),(0,[z1,z526,z2,z3,z4,z5,z8]),(0,[z1,z2,z213,z3,z4,z5,z8])],[(0,[z527,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z288,z4,z5,z8]),(0,[z1,z2,z3,z528,z4,z5,z8])],[(0,[z529,z1,z2,z3,z4,z5,z8]),(0,[z103,z1,z2,z3,z4,z5,z86]),(0,[z1,z2,z147,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z530]),(0,[z115,z1,z2,z3,z4,z5,z10]),(0,[z1,z531,z2,z3,z4,z5,z8]),(0,[z141,z1,z2,z3,z69,z5,z8]),(0,[z179,z1,z2,z3,z4,z5,z10])],[(0,[z532,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z533,z5,z8]),(0,[z1,z2,z67,z4,z26,z5,z8]),(0,[z1,z2,z3,z4,z5,z53,z8]),(0,[z1,z2,z3,z4,z5,z8,z40])],[(0,[z534,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z535,z8]),(0,[z1,z2,z3,z4,z5,z536,z8])],[(0,[z22,z1,z2,z3,z4,z5,z537]),(0,[z1,z2,z3,z538,z4,z5,z8]),(1,[z1,z2,z185,z4,z5,z8]),(0,[z1,z539,z2,z3,z4,z5,z8]),(0,[z1,z540,z2,z3,z4,z5,z8]),(0,[z1,z541,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z143,z69,z4,z5])]],
   [[(0,[z1,z2,z3,z4,z5,z542,z8]),(0,[z110,z1,z2,z3,z230,z5,z8]),(1,[z1,z274,z3,z4,z5,z8]),(1,[z1,z2,z3,z338,z5,z8]),(0,[z1,z18,z2,z3,z44,z4,z5]),(0,[z1,z18,z2,z147,z3,z4,z5]),(0,[z1,z85,z2,z50,z3,z4,z5]),(0,[z1,z18,z2,z50,z3,z4,z5]),(0,[z1,z2,z3,z4,z543,z5,z8])],[(0,[z71,z1,z2,z147,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z544,z8]),(0,[z1,z2,z3,z4,z545,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z546]),(0,[z1,z2,z3,z547,z4,z5,z8])],[(0,[z1,z2,z3,z20,z4,z5,z8]),(0,[z1,z548,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z549,z5,z8]),(1,[z167,z1,z3,z117,z5,z8]),(0,[z550,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z175,z5,z8]),(0,[z551,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z117,z5,z10]),(1,[z1,z152,z3,z4,z5,z8])],[(0,[z1,z2,z3,z552,z4,z5,z8]),(0,[z1,z553,z2,z3,z4,z5,z8]),(0,[z24,z1,z2,z3,z4,z5,z8]),(0,[z0,z37,z1,z2,z3,z4,z8]),(0,[z1,z2,z3,z4,z5,z215,z8]),(0,[z554,z1,z2,z3,z4,z5,z8]),(0,[z1,z555,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z556,z4,z5,z8])],[(0,[z1,z557,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z98,z8]),(0,[z1,z18,z2,z66,z3,z4,z5]),(0,[z132,z1,z2,z3,z4,z53,z8]),(0,[z558,z1,z2,z3,z4,z5,z8])],[(0,[z559,z1,z2,z3,z4,z5,z8]),(0,[z1,z18,z2,z3,z67,z4,z5])]],
   [[(0,[z560,z1,z2,z3,z4,z5,z8])],[(0,[z561,z1,z2,z3,z4,z5,z8]),(0,[z1,z494,z2,z3,z4,z5,z8])],[(0,[z99,z2,z19,z3,z4,z5,z8]),(0,[z1,z2,z562,z3,z4,z5,z8]),(0,[z1,z563,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z14]),(0,[z1,z2,z3,z4,z564,z5,z8]),(0,[z1,z2,z565,z3,z4,z5,z8]),(0,[z1,z540,z18,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z566,z5,z8]),(0,[z1,z2,z3,z4,z567,z5,z8]),(0,[z1,z568,z2,z3,z4,z5,z8])],[(0,[z569,z1,z2,z3,z4,z5,z8]),(0,[z1,z18,z2,z3,z123,z4,z5]),(1,[z1,z2,z3,z4,z98,z8]),(0,[z570,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z571,z5,z8])],[(0,[z103,z1,z2,z3,z4,z9,z5]),(0,[z29,z1,z2,z4,z26,z5,z8]),(0,[z572,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z573,z5,z8])],[(0,[z574,z1,z2,z3,z4,z5,z8]),(0,[z1,z575,z2,z3,z4,z5,z8]),(0,[z576,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z10,z204]),(0,[z1,z2,z3,z69,z5,z8,z40]),(0,[z1,z270,z2,z3,z4,z5,z8])]],
   [[(0,[z1,z2,z66,z3,z4,z5,z8]),(1,[z1,z2,z3,z528,z4,z5]),(0,[z1,z18,z2,z3,z4,z292,z5])],[(0,[z558,z1,z18,z2,z3,z4,z5])],[(0,[z1,z577,z2,z3,z4,z5,z8]),(0,[z171,z1,z18,z2,z3,z4,z5]),(0,[z198,z1,z2,z3,z4,z5,z86]),(0,[z1,z2,z3,z347,z4,z5,z8]),(0,[z1,z2,z578,z3,z4,z5,z8]),(0,[z90,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z10,z40])],[(0,[z1,z2,z3,z4,z579,z5,z8]),(0,[z0,z1,z2,z3,z291,z5,z8]),(1,[z1,z2,z3,z4,z5,z138])],[(0,[z1,z2,z580,z3,z4,z5,z8]),(0,[z581,z1,z2,z3,z4,z5,z8]),(0,[z582,z1,z2,z3,z4,z5,z8])],[(0,[z71,z1,z2,z44,z4,z5,z8]),(0,[z1,z2,z3,z347,z44,z4,z5]),(0,[z1,z2,z583,z3,z4,z5,z8]),(0,[z1,z2,z3,z584,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z154]),(0,[z1,z2,z3,z585,z4,z5,z8]),(0,[z37,z1,z18,z2,z3,z4,z5])],[(0,[z1,z2,z3,z586,z4,z5,z8]),(0,[z587,z1,z2,z3,z4,z5,z8]),(0,[z2,z3,z230,z4,z111,z5,z8]),(0,[z1,z2,z3,z4,z5,z588,z8]),(0,[z1,z2,z3,z4,z175,z5,z204]),(0,[z1,z146,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z589,z8]),(0,[z590,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z10,z51]),(0,[z1,z2,z3,z4,z292,z5,z8])],[(0,[z1,z2,z3,z254,z4,z5,z10]),(0,[z591,z1,z2,z3,z4,z5,z8]),(0,[z1,z85,z2,z3,z69,z4,z5]),(0,[z1,z2,z3,z67,z4,z5,z8]),(0,[z1,z2,z3,z592,z4,z5,z8])]],
   [[(0,[z593,z1,z2,z3,z4,z5,z8]),(0,[z118,z1,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z69,z5,z40]),(1,[z1,z2,z3,z4,z292,z10]),(0,[z411,z1,z18,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z8,z537]),(0,[z1,z2,z3,z4,z594,z5,z8]),(1,[z1,z2,z3,z4,z5,z284]),(0,[z1,z18,z2,z3,z4,z595,z5])],[(1,[z0,z1,z2,z3,z4,z10]),(0,[z1,z596,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z595,z5,z8])],[],[(0,[z1,z2,z3,z597,z4,z5,z8]),(0,[z1,z2,z598,z3,z4,z5,z8]),(0,[z1,z599,z2,z3,z4,z5,z8]),(0,[z34,z1,z18,z2,z3,z4,z5])],[(0,[z600,z1,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z537]),(0,[z2,z3,z4,z5,z86,z8,z204]),(0,[z1,z2,z3,z4,z601,z5,z8]),(0,[z1,z2,z3,z4,z602,z5,z8])],[(0,[z1,z2,z3,z4,z603,z5,z8]),(0,[z118,z1,z32,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z159])],[(0,[z604,z1,z2,z3,z4,z5,z8]),(0,[z1,z605,z2,z3,z4,z5,z8]),(0,[z103,z1,z2,z3,z4,z5,z8])]],
   [[(0,[z94,z1,z2,z3,z4,z5,z10]),(0,[z1,z2,z3,z230,z4,z5,z8]),(0,[z118,z1,z2,z3,z4,z201,z8])],[(0,[z1,z2,z3,z4,z5,z86,z8]),(0,[z1,z606,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z607,z4,z5,z8]),(0,[z1,z32,z2,z3,z4,z196,z5]),(0,[z1,z2,z3,z4,z608,z5,z8])],[(0,[z1,z2,z3,z291,z4,z5,z8]),(0,[z1,z2,z3,z4,z175,z5,z86]),(0,[z609,z1,z2,z3,z4,z5,z8]),(0,[z1,z87,z2,z66,z3,z5,z8]),(0,[z68,z1,z18,z2,z3,z4,z5]),(0,[z610,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z611,z8])],[(0,[z1,z2,z3,z4,z612,z5,z8]),(0,[z1,z18,z2,z3,z4,z49,z5])],[(0,[z110,z1,z2,z3,z4,z5,z8]),(1,[z404,z2,z3,z230,z5,z8]),(0,[z1,z146,z3,z4,z117,z5,z8]),(0,[z1,z2,z3,z613,z4,z5,z8]),(0,[z1,z2,z614,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z8,z615]),(1,[z1,z121,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z616,z5,z8])],[(0,[z617,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z618,z3,z4,z5,z8]),(0,[z24,z1,z2,z3,z4,z215,z8]),(0,[z167,z1,z2,z3,z4,z5,z10]),(0,[z1,z2,z3,z4,z403,z5,z8]),(1,[z1,z2,z50,z4,z5,z51]),(0,[z1,z18,z2,z3,z4,z5,z5])],[(0,[z1,z2,z3,z619,z4,z5,z8]),(0,[z620,z1,z2,z3,z4,z5,z8])]],
   [[(0,[z182,z1,z2,z3,z4,z5,z10]),(0,[z1,z2,z3,z4,z621,z5,z8]),(0,[z1,z2,z3,z622,z4,z5,z8]),(0,[z1,z87,z2,z3,z123,z5,z8]),(0,[z1,z623,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z5,z10])],[(1,[z171,z2,z172,z4,z5,z8]),(0,[z167,z1,z2,z613,z4,z5,z8]),(0,[z1,z2,z3,z4,z624,z5,z8]),(0,[z1,z2,z3,z4,z49,z5,z530]),(0,[z1,z625,z2,z3,z4,z5,z8])],[(0,[z626,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z627,z5,z8]),(0,[z1,z2,z3,z4,z628,z5,z8]),(0,[z1,z2,z3,z4,z629,z5,z8]),(0,[z103,z1,z18,z2,z3,z4,z5]),(0,[z630,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z10]),(0,[z1,z18,z2,z3,z91,z4,z5])],[(0,[z631,z1,z2,z3,z4,z5,z8]),(1,[z68,z1,z2,z4,z49,z8])],[(0,[z1,z2,z2,z3,z4,z5,z8]),(0,[z632,z1,z2,z3,z4,z5,z8]),(0,[z633,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z634,z4,z5,z8]),(0,[z1,z2,z3,z230,z5,z53,z8]),(1,[z1,z2,z3,z113,z5,z8]),(0,[z71,z1,z18,z2,z3,z4,z5]),(0,[z167,z1,z2,z3,z117,z5,z8])],[(0,[z1,z2,z3,z635,z4,z5,z8]),(0,[z103,z1,z85,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z636,z8]),(0,[z1,z2,z3,z4,z637,z5,z8]),(0,[z1,z2,z3,z4,z5,z638,z8]),(0,[z1,z2,z3,z4,z5,z353,z8])],[(0,[z639,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z640,z8]),(0,[z1,z2,z3,z106,z52,z4,z8]),(0,[z37,z1,z18,z2,z3,z4,z8])]],
   [[(0,[z1,z2,z3,z4,z5,z56,z8]),(0,[z1,z2,z3,z4,z111,z5,z8]),(0,[z1,z2,z3,z4,z5,z381,z8]),(0,[z1,z2,z3,z4,z5,z201,z10]),(0,[z641,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z362,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z642,z8]),(0,[z643,z1,z2,z3,z4,z5,z8]),(0,[z182,z171,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z111,z5,z53,z8]),(1,[z1,z2,z613,z4,z5,z8]),(0,[z1,z2,z3,z644,z4,z5,z8]),(0,[z1,z18,z85,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z645,z5,z8]),(0,[z141,z1,z18,z2,z3,z4,z5])],[(0,[z103,z1,z2,z3,z4,z5,z204]),(0,[z1,z2,z66,z147,z4,z5,z8]),(0,[z1,z85,z3,z4,z5,z8,z159]),(0,[z132,z1,z2,z3,z4,z5,z10]),(0,[z1,z2,z3,z4,z149,z5,z8])],[(0,[z1,z2,z172,z3,z4,z5,z10]),(0,[z1,z2,z3,z4,z92,z5,z8]),(1,[z1,z2,z4,z403,z5,z8]),(1,[z228,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z528,z52,z4,z5])],[(0,[z1,z2,z3,z4,z5,z646,z8]),(0,[z1,z2,z3,z4,z5,z8,z647]),(0,[z1,z2,z3,z4,z648,z5,z8]),(0,[z1,z2,z3,z4,z5,z649,z8]),(0,[z650,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z651,z5,z8]),(0,[z118,z1,z2,z3,z4,z287,z8]),(0,[z1,z2,z3,z4,z5,z652,z8]),(0,[z1,z2,z3,z143,z5,z8,z40]),(0,[z630,z1,z18,z2,z3,z4,z5])],[(0,[z1,z653,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z201,z10]),(0,[z1,z2,z3,z654,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z86,z40]),(0,[z655,z1,z2,z3,z4,z5,z8]),(1,[z1,z2,z500,z3,z4,z5]),(0,[z1,z2,z3,z656,z4,z5,z8])]],
   [[(0,[z1,z657,z2,z3,z4,z5,z8]),(0,[z1,z658,z2,z3,z4,z5,z8]),(0,[z1,z146,z2,z147,z4,z5,z8]),(0,[z1,z2,z3,z123,z4,z5,z8])],[(0,[z659,z1,z2,z3,z4,z5,z8]),(0,[z1,z87,z146,z3,z4,z5,z8]),(0,[z1,z2,z3,z660,z4,z5,z8]),(0,[z661,z1,z2,z3,z4,z5,z8]),(0,[z1,z18,z2,z13,z3,z4,z5])],[(0,[z94,z2,z19,z3,z4,z5,z8]),(0,[z1,z662,z2,z3,z4,z5,z8]),(0,[z663,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z313]),(0,[z1,z2,z3,z106,z4,z5,z546])],[(1,[z182,z2,z254,z4,z5,z8]),(0,[z1,z2,z664,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z86,z51]),(0,[z1,z2,z3,z4,z665,z5,z8])],[],[(0,[z1,z666,z2,z3,z4,z5,z8]),(0,[z667,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z295,z117,z5]),(1,[z1,z2,z3,z4,z196,z5])],[(0,[z1,z2,z668,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z669]),(1,[z1,z2,z3,z4,z5,z313]),(0,[z670,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z31]),(1,[z103,z1,z3,z4,z9,z5]),(0,[z1,z2,z50,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z8,z671]),(0,[z404,z1,z2,z3,z111,z5,z8]),(0,[z672,z1,z2,z3,z4,z5,z8]),(0,[z1,z18,z2,z3,z4,z175,z5]),(0,[z132,z1,z2,z3,z106,z4,z8])]],
   [[(0,[z1,z2,z3,z4,z673,z5,z8]),(0,[z674,z1,z2,z3,z4,z5,z8]),(0,[z71,z1,z146,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z675,z8]),(0,[z1,z18,z146,z2,z3,z4,z5]),(0,[z1,z85,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z52,z4,z5,z8]),(0,[z1,z18,z2,z3,z4,z5,z8]),(0,[z1,z2,z676,z3,z4,z5,z8])],[(0,[z404,z1,z2,z3,z4,z5,z8]),(0,[z198,z1,z18,z2,z3,z4,z5]),(0,[z1,z2,z677,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z678,z5,z8])],[(0,[z110,z1,z2,z3,z4,z5,z386]),(0,[z1,z2,z3,z679,z4,z5,z8]),(0,[z1,z2,z3,z4,z680,z5,z8]),(1,[z1,z2,z3,z4,z5,z530])],[(0,[z681,z1,z2,z3,z4,z5,z8]),(1,[z45,z1,z2,z3,z4,z5]),(0,[z1,z18,z2,z3,z4,z287,z5]),(0,[z682,z1,z2,z3,z4,z5,z8]),(0,[z683,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z684,z5,z8]),(0,[z515,z1,z18,z2,z3,z4,z5])],[(0,[z1,z2,z685,z3,z4,z5,z8]),(0,[z110,z1,z2,z3,z4,z5,z332]),(0,[z1,z2,z3,z4,z287,z5,z10])],[(0,[z1,z329,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z69,z4,z5,z8])],[(0,[z1,z2,z66,z44,z4,z5,z8]),(0,[z1,z2,z3,z4,z287,z8,z10]),(0,[z1,z2,z3,z686,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z687,z8])],[(0,[z1,z688,z2,z3,z4,z5,z8]),(0,[z689,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z33,z5,z8])]],
   [[(0,[z1,z2,z3,z4,z690,z5,z8]),(0,[z1,z2,z3,z4,z691,z5,z8]),(0,[z102,z1,z2,z4,z117,z5,z8]),(1,[z1,z2,z3,z4,z5,z546])],[(0,[z1,z2,z3,z4,z5,z692,z8]),(1,[z1,z2,z3,z4,z5,z381]),(0,[z198,z1,z2,z3,z4,z5,z204]),(1,[z1,z2,z3,z216,z5,z8]),(0,[z693,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z694])],[(0,[z695,z1,z2,z3,z4,z5,z8]),(0,[z672,z1,z18,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z696,z5,z8]),(0,[z171,z1,z2,z3,z4,z5,z10]),(0,[z1,z32,z3,z4,z5,z201,z8]),(1,[z1,z2,z3,z4,z287,z10])],[(0,[z1,z697,z2,z3,z4,z5,z8]),(0,[z404,z1,z18,z2,z3,z4,z5]),(0,[z1,z146,z2,z44,z4,z5,z8]),(0,[z1,z2,z3,z698,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z699]),(0,[z1,z2,z700,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z8,z312]),(0,[z1,z701,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z702]),(0,[z703,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z52,z5,z53,z8]),(0,[z704,z1,z2,z3,z4,z5,z8])],[(0,[z705,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z706,z3,z4,z5,z8]),(0,[z37,z1,z2,z3,z4,z5,z10])],[]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z2,z3,z4,z5,z707]),(0,[z171,z2,z172,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z708])],[(0,[z1,z18,z2,z185,z4,z5]),(0,[z84,z1,z2,z3,z4,z127]),(0,[z1,z146,z147,z4,z5,z8]),(0,[z1,z2,z709,z4,z5,z8])],[(0,[z1,z18,z2,z3,z216,z5]),(0,[z1,z18,z2,z613,z4,z5]),(0,[z1,z2,z3,z4,z287,z14]),(0,[z68,z1,z2,z4,z49,z8])],[(0,[z1,z710,z3,z4,z5,z8]),(0,[z167,z1,z403,z117,z5,z8]),(0,[z1,z2,z3,z69,z410,z5]),(0,[z1,z711,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z712]),(0,[z1,z2,z3,z113,z5,z8]),(0,[z1,z2,z3,z4,z5,z713]),(0,[z1,z3,z613,z117,z5,z8])],[(0,[z1,z2,z3,z4,z5,z10]),(0,[z1,z2,z714,z4,z5,z8]),(0,[z1,z715,z251,z3,z4,z5]),(0,[z551,z1,z2,z3,z4,z10])],[(0,[z1,z716,z2,z3,z4,z5]),(0,[z1,z2,z3,z717,z4,z8]),(0,[z1,z44,z117,z26,z5,z8]),(0,[z1,z79,z3,z4,z287,z8]),(0,[z103,z1,z3,z4,z718,z5])],[(0,[z1,z2,z3,z719,z4,z5]),(0,[z1,z2,z4,z720,z5,z51])]],
   [[(0,[z721,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z57,z10]),(0,[z1,z2,z613,z4,z5,z8]),(0,[z1,z85,z3,z4,z5,z159])],[(0,[z1,z2,z121,z3,z4,z10]),(0,[z1,z2,z3,z4,z5,z722])],[(0,[z22,z1,z2,z3,z4,z723]),(0,[z1,z274,z3,z4,z5,z6]),(0,[z316,z2,z3,z4,z5,z204]),(0,[z1,z2,z4,z403,z5,z8]),(0,[z1,z87,z613,z4,z5,z8]),(1,[z1,z2,z4,z724,z8])],[(0,[z1,z2,z3,z4,z5,z56]),(0,[z1,z87,z251,z3,z5,z8])],[(0,[z1,z2,z725,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z726]),(0,[z0,z1,z2,z3,z291,z10]),(0,[z1,z18,z2,z3,z4,z510]),(0,[z1,z2,z727,z4,z5,z8])],[(0,[z94,z728,z3,z4,z5,z8]),(0,[z1,z2,z729,z4,z5,z8]),(0,[z0,z2,z3,z4,z215,z10]),(0,[z511,z1,z44,z4,z5,z8]),(0,[z1,z2,z3,z4,z201,z10]),(0,[z730,z1,z2,z3,z4,z5]),(0,[z1,z18,z2,z3,z4,z98]),(0,[z1,z3,z4,z718,z5,z159]),(0,[z1,z731,z2,z3,z4,z5]),(0,[z1,z2,z3,z732,z5,z10])],[(0,[z1,z2,z3,z4,z5,z733]),(0,[z1,z2,z3,z4,z127,z10]),(0,[z1,z2,z500,z3,z4,z5]),(0,[z68,z1,z2,z4,z724,z8]),(0,[z1,z575,z2,z3,z4,z10])],[(0,[z1,z2,z3,z4,z56,z723]),(0,[z156,z2,z254,z4,z5,z8]),(0,[z1,z734,z2,z3,z4,z5]),(0,[z0,z24,z2,z3,z4,z10]),(0,[z1,z2,z3,z4,z149,z5])]],
   [[(0,[z1,z2,z3,z4,z5,z735]),(0,[z1,z2,z3,z4,z736,z8]),(0,[z1,z2,z3,z4,z5,z737]),(0,[z1,z2,z3,z4,z5,z738]),(0,[z198,z2,z3,z4,z5,z204]),(0,[z1,z2,z3,z4,z5,z739]),(1,[z1,z251,z26,z5,z8]),(0,[z1,z2,z3,z4,z5,z740])],[(0,[z1,z2,z3,z4,z5,z741]),(0,[z1,z2,z742,z4,z5,z8]),(0,[z1,z2,z3,z4,z330,z10]),(0,[z1,z224,z3,z4,z9,z5])],[(0,[z1,z2,z3,z4,z5,z743]),(0,[z182,z2,z254,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z744])],[(0,[z24,z2,z3,z4,z23,z10]),(0,[z1,z2,z3,z745,z5,z8]),(0,[z1,z2,z3,z4,z5,z746]),(0,[z1,z32,z3,z4,z201,z10]),(0,[z118,z1,z500,z3,z4,z287]),(0,[z1,z2,z747,z3,z4,z5])],[(0,[z128,z1,z2,z3,z5,z8]),(0,[z115,z1,z2,z3,z4,z98]),(0,[z1,z2,z3,z143,z91,z5])],[(0,[z1,z2,z3,z4,z748,z8]),(0,[z1,z2,z3,z4,z5,z313]),(0,[z1,z2,z3,z4,z5,z749]),(0,[z1,z2,z613,z123,z5,z8]),(0,[z103,z1,z3,z4,z9,z5]),(0,[z672,z1,z442,z3,z4,z5])],[(0,[z182,z2,z254,z4,z5,z309]),(0,[z0,z18,z2,z3,z4,z215])],[(0,[z1,z2,z3,z4,z750,z5]),(0,[z1,z751,z3,z4,z5,z8]),(0,[z1,z2,z752,z4,z5,z8]),(0,[z1,z2,z3,z4,z344,z10])]],
   [[(0,[z1,z121,z3,z4,z5,z381]),(0,[z195,z24,z2,z3,z4,z10]),(0,[z1,z2,z3,z4,z5,z753]),(1,[z1,z613,z117,z5,z8]),(0,[z1,z2,z754,z4,z5,z8]),(0,[z29,z1,z18,z2,z26,z5]),(0,[z195,z2,z3,z4,z5,z312])],[(0,[z1,z2,z3,z4,z755,z8]),(0,[z756,z1,z3,z4,z5,z8]),(0,[z1,z2,z20,z4,z5,z6]),(0,[z68,z1,z2,z288,z4,z49]),(0,[z411,z1,z2,z3,z91,z5])],[(0,[z1,z2,z3,z757,z5,z8]),(0,[z1,z2,z185,z4,z5,z10]),(0,[z45,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z758]),(0,[z1,z2,z3,z4,z368,z10])],[(0,[z1,z2,z3,z4,z5,z759]),(0,[z1,z2,z3,z338,z5,z10]),(0,[z1,z87,z3,z760,z5,z8]),(0,[z532,z1,z2,z3,z4,z10]),(0,[z1,z2,z13,z4,z175,z5])],[(0,[z24,z2,z3,z4,z353,z10]),(0,[z102,z1,z2,z4,z295,z5]),(0,[z1,z2,z761,z3,z4,z287])],[(0,[z0,z1,z2,z3,z4,z762]),(0,[z1,z2,z240,z4,z5,z51]),(0,[z1,z2,z3,z763,z5,z8]),(0,[z1,z2,z3,z4,z256,z10])],[(0,[z1,z2,z3,z4,z5,z764]),(0,[z1,z765,z2,z3,z4,z5]),(0,[z167,z1,z3,z117,z5,z10]),(0,[z1,z2,z3,z4,z5,z766]),(0,[z1,z2,z3,z4,z255,z10])],[(0,[z1,z2,z3,z4,z5,z767]),(0,[z768,z2,z3,z4,z5,z8]),(0,[z167,z102,z1,z117,z5,z8]),(0,[z1,z3,z4,z760,z5,z8]),(0,[z1,z152,z3,z4,z5,z10])]],
   [[(0,[z1,z769,z2,z3,z4,z8]),(0,[z1,z18,z2,z3,z92,z5]),(0,[z1,z2,z3,z216,z5,z8]),(0,[z1,z2,z3,z4,z5,z770]),(0,[z771,z18,z2,z3,z4,z5])],[(0,[z1,z728,z3,z4,z5,z8]),(0,[z22,z99,z3,z4,z5,z10]),(0,[z1,z121,z20,z4,z5,z8]),(0,[z1,z2,z3,z92,z5,z381]),(0,[z167,z1,z613,z117,z5,z8])],[(0,[z2,z3,z4,z23,z772,z8]),(0,[z1,z251,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z287,z10])],[(0,[z1,z2,z773,z4,z5,z8]),(0,[z103,z1,z3,z4,z126,z5])],[(0,[z1,z2,z774,z4,z5,z8]),(0,[z71,z1,z18,z44,z4,z5]),(0,[z1,z2,z775,z4,z5,z8])],[(0,[z1,z3,z4,z776,z5,z8]),(0,[z1,z2,z777,z4,z5,z8]),(0,[z1,z2,z3,z4,z778,z5]),(0,[z1,z3,z123,z760,z5,z8])],[(0,[z1,z2,z3,z779,z5,z8]),(0,[z1,z2,z3,z4,z780,z5]),(0,[z0,z1,z2,z185,z4,z10]),(0,[z1,z2,z3,z41,z5,z40])],[(0,[z22,z99,z3,z4,z5,z56]),(0,[z110,z2,z3,z111,z5,z386]),(0,[z1,z2,z3,z781,z4,z5]),(0,[z1,z2,z3,z4,z98,z10])]],
   [[(0,[z1,z2,z3,z4,z5,z782]),(0,[z1,z2,z3,z4,z5,z783]),(0,[z784,z1,z2,z3,z4,z5]),(0,[z650,z1,z2,z3,z4,z10]),(0,[z1,z785,z3,z4,z5,z10])],[(0,[z110,z2,z3,z111,z5,z332]),(0,[z1,z2,z369,z3,z4,z10]),(1,[z2,z3,z4,z5,z786]),(0,[z1,z2,z3,z4,z720,z5])],[(0,[z1,z2,z20,z92,z5,z8]),(0,[z1,z2,z67,z447,z5,z8]),(0,[z1,z2,z3,z4,z787,z8])],[(0,[z37,z1,z121,z3,z4,z8]),(0,[z1,z18,z2,z3,z4,z385])],[(0,[z1,z653,z2,z3,z4,z10]),(0,[z102,z1,z44,z4,z5,z8]),(0,[z1,z32,z3,z4,z196,z201]),(0,[z1,z18,z2,z3,z4,z272])],[(0,[z1,z2,z3,z788,z5,z8]),(0,[z1,z789,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z790,z8]),(0,[z1,z2,z3,z791,z5,z8]),(0,[z363,z99,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z627,z10]),(0,[z792,z2,z3,z4,z5,z8]),(0,[z45,z1,z2,z3,z338,z5]),(0,[z1,z2,z3,z528,z52,z53])],[(0,[z1,z2,z3,z4,z793,z8]),(0,[z1,z794,z2,z3,z4,z5]),(0,[z198,z2,z3,z4,z5,z786]),(0,[z1,z2,z136,z4,z724,z8])]],
   [[(0,[z1,z2,z3,z795,z5,z8]),(0,[z1,z2,z3,z143,z4,z127]),(0,[z118,z1,z3,z4,z287,z8]),(0,[z1,z2,z3,z288,z4,z5])],[(0,[z1,z2,z3,z4,z5,z796]),(0,[z1,z2,z3,z291,z5,z8]),(0,[z1,z2,z797,z4,z5,z8])],[(0,[z728,z19,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z798]),(0,[z1,z2,z136,z4,z192,z8]),(0,[z1,z799,z2,z3,z4,z5]),(0,[z558,z207,z2,z3,z4,z5]),(0,[z515,z1,z2,z439,z4,z5])],[(0,[z94,z19,z3,z4,z5,z8]),(0,[z1,z2,z800,z4,z5,z8]),(0,[z1,z2,z801,z3,z4,z5])],[(0,[z118,z1,z18,z3,z4,z287]),(0,[z1,z18,z251,z3,z4,z5])],[],[(0,[z1,z274,z3,z4,z5,z381]),(0,[z2,z3,z4,z5,z786,z204]),(0,[z1,z802,z3,z4,z5,z8]),(0,[z803,z2,z3,z4,z5,z8]),(0,[z125,z1,z2,z3,z362,z5])],[(0,[z1,z146,z804,z4,z5,z8]),(0,[z193,z1,z2,z4,z170,z5])]],
   [[(0,[z1,z2,z805,z4,z5,z8]),(0,[z118,z1,z3,z4,z806,z8]),(0,[z103,z1,z578,z3,z4,z5]),(0,[z29,z1,z251,z26,z5,z8]),(0,[z132,z1,z2,z3,z106,z149])],[(0,[z1,z2,z3,z4,z807,z5]),(0,[z0,z2,z3,z291,z215,z8]),(0,[z71,z128,z1,z44,z5,z8])],[(0,[z22,z18,z99,z3,z4,z5]),(0,[z1,z2,z808,z4,z5,z8]),(0,[z24,z329,z2,z3,z4,z23]),(0,[z102,z1,z2,z4,z5,z8]),(0,[z128,z1,z2,z3,z347,z5])],[(0,[z809,z1,z2,z3,z4,z5]),(0,[z810,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z811,z5,z8])],[(0,[z812,z1,z2,z3,z5,z8]),(0,[z71,z128,z1,z2,z5,z8]),(0,[z1,z2,z3,z4,z5,z813]),(0,[z1,z18,z164,z2,z3,z4]),(0,[z68,z1,z18,z2,z4,z49])],[(0,[z1,z2,z3,z4,z814,z8]),(0,[z1,z2,z3,z4,z300,z10]),(0,[z1,z18,z2,z3,z4,z157]),(0,[z1,z2,z3,z815,z52,z8]),(0,[z1,z2,z3,z4,z816,z5]),(0,[z1,z2,z213,z4,z5,z154])],[(0,[z1,z146,z3,z216,z5,z8]),(0,[z1,z18,z2,z3,z4,z296])],[(0,[z1,z817,z3,z4,z5,z8]),(0,[z404,z2,z3,z230,z5,z10]),(0,[z1,z274,z20,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z818]),(0,[z1,z2,z3,z4,z648,z10]),(0,[z1,z2,z3,z819,z4,z5]),(0,[z820,z2,z3,z4,z5,z8]),(0,[z1,z2,z4,z821,z5,z8])]],
   [[(0,[z1,z121,z3,z4,z5,z10]),(0,[z2,z3,z4,z5,z822,z8])],[(0,[z1,z823,z2,z3,z4,z5]),(0,[z84,z1,z2,z3,z4,z10]),(0,[z65,z166,z2,z3,z4,z86]),(0,[z824,z2,z3,z4,z5,z8])],[(0,[z1,z121,z3,z4,z8,z10]),(0,[z1,z2,z147,z216,z5,z8]),(0,[z1,z2,z3,z4,z5,z825]),(0,[z102,z1,z2,z67,z5,z8])],[(0,[z826,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z827,z4,z5])],[(0,[z71,z1,z44,z4,z5,z8]),(0,[z1,z146,z4,z680,z5,z8]),(0,[z1,z2,z3,z4,z828,z5]),(0,[z558,z1,z2,z3,z4,z10])],[(0,[z1,z2,z20,z4,z5,z381]),(0,[z0,z1,z2,z3,z92,z10]),(0,[z271,z1,z2,z26,z5,z8]),(0,[z1,z2,z3,z4,z829,z5]),(0,[z1,z2,z3,z4,z830,z5]),(0,[z1,z2,z3,z4,z464,z10]),(0,[z1,z540,z224,z3,z4,z5])],[(0,[z1,z2,z3,z4,z831,z8]),(0,[z1,z2,z185,z291,z5,z8]),(0,[z71,z1,z347,z44,z4,z5]),(0,[z1,z2,z4,z832,z5,z8])],[(0,[z833,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z834,z5]),(0,[z1,z2,z3,z4,z5,z835])]],
   [[],[(0,[z1,z2,z3,z92,z5,z10]),(0,[z198,z1,z2,z3,z4,z127]),(0,[z1,z2,z3,z836,z4,z5])],[(0,[z1,z2,z837,z4,z5,z8]),(0,[z1,z838,z2,z3,z4,z5]),(0,[z128,z1,z2,z613,z5,z8]),(0,[z1,z87,z3,z114,z5,z8]),(0,[z1,z2,z3,z4,z5,z839])],[(0,[z68,z1,z2,z4,z57,z8]),(0,[z29,z1,z701,z2,z5,z8]),(0,[z1,z2,z50,z4,z720,z5])],[(0,[z110,z2,z3,z111,z5,z8]),(0,[z1,z799,z2,z3,z4,z8])],[(0,[z1,z2,z3,z840,z5,z8]),(0,[z1,z2,z841,z4,z5,z8]),(0,[z1,z842,z3,z4,z5,z8]),(0,[z0,z2,z3,z4,z772,z8]),(0,[z1,z2,z3,z4,z483,z10]),(0,[z1,z2,z761,z3,z4,z10]),(0,[z1,z2,z3,z4,z5,z843]),(0,[z1,z625,z2,z3,z4,z10])],[(0,[z1,z2,z844,z4,z5,z8]),(0,[z1,z2,z3,z4,z845,z5]),(0,[z1,z3,z4,z846,z5,z8])],[(0,[z1,z847,z2,z3,z4,z5]),(0,[z465,z1,z3,z117,z5,z8]),(0,[z141,z1,z2,z3,z4,z98]),(0,[z1,z3,z4,z718,z5,z8]),(0,[z1,z2,z136,z4,z105,z192]),(0,[z1,z2,z4,z175,z720,z5])]],
   [[(0,[z1,z2,z3,z4,z723,z8]),(0,[z118,z1,z3,z4,z287,z390]),(0,[z1,z2,z3,z4,z5,z848])],[(0,[z849,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z850]),(0,[z851,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z852]),(0,[z1,z2,z168,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z853]),(0,[z1,z2,z3,z4,z5,z854]),(0,[z1,z2,z3,z4,z5,z855]),(0,[z1,z2,z3,z4,z5,z856]),(0,[z857,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z858,z5,z8]),(0,[z1,z2,z3,z4,z642,z10]),(0,[z1,z2,z3,z4,z5,z183]),(0,[z1,z859,z2,z3,z4,z5]),(0,[z1,z18,z2,z168,z4,z5])],[(0,[z1,z2,z860,z4,z5,z8]),(0,[z1,z2,z3,z52,z53,z8])],[(0,[z861,z1,z2,z3,z4,z5])],[(0,[z1,z2,z66,z821,z5,z8])],[(0,[z1,z2,z44,z216,z5,z8]),(0,[z1,z2,z3,z4,z652,z10]),(0,[z1,z862,z3,z4,z5,z8]),(0,[z1,z18,z2,z3,z52,z53])],[(1,[z728,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z863]),(0,[z167,z1,z3,z295,z117,z5]),(0,[z1,z87,z3,z123,z5,z10]),(0,[z29,z1,z2,z26,z5,z10])]],
   [[(0,[z532,z19,z3,z4,z5,z8]),(0,[z1,z864,z2,z3,z4,z5]),(0,[z182,z18,z2,z254,z4,z5]),(0,[z1,z2,z3,z865,z5,z8]),(1,[z1,z804,z4,z5,z8]),(0,[z1,z2,z3,z4,z866,z5])],[(0,[z132,z1,z2,z3,z321,z8])],[(0,[z1,z2,z3,z4,z373,z10]),(0,[z68,z1,z2,z4,z49,z530])],[(0,[z1,z2,z3,z4,z5,z867]),(0,[z128,z1,z146,z2,z5,z8]),(0,[z102,z1,z2,z26,z5,z8]),(0,[z1,z18,z2,z3,z120,z4])],[(0,[z1,z2,z868,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z869]),(0,[z102,z1,z146,z4,z5,z8]),(0,[z1,z2,z3,z760,z5,z8]),(0,[z1,z18,z152,z3,z4,z5])],[(0,[z643,z1,z2,z3,z4,z10]),(0,[z1,z2,z3,z4,z5,z870]),(0,[z128,z1,z87,z3,z5,z8]),(0,[z1,z18,z2,z3,z4,z645])],[(0,[z1,z357,z2,z3,z4,z10]),(0,[z1,z274,z3,z4,z5,z10]),(0,[z1,z2,z3,z4,z98,z159])],[(0,[z1,z2,z3,z871,z5,z8]),(0,[z128,z1,z2,z66,z5,z8])]],
   [[(0,[z1,z2,z3,z4,z806,z8]),(0,[z29,z1,z152,z26,z5,z8])],[(0,[z24,z1,z2,z3,z4,z313]),(0,[z1,z2,z872,z4,z5,z8]),(0,[z1,z2,z517,z67,z5,z8]),(0,[z1,z2,z136,z4,z192,z284]),(0,[z84,z494,z2,z3,z4,z5])],[(0,[z115,z1,z2,z4,z170,z5]),(0,[z1,z2,z3,z4,z535,z10])],[(0,[z22,z728,z3,z4,z5,z8]),(0,[z873,z1,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z874]),(0,[z1,z2,z3,z291,z5,z6]),(0,[z482,z1,z2,z4,z175,z5]),(0,[z1,z2,z3,z4,z5,z875])],[(0,[z1,z2,z3,z4,z5,z876]),(0,[z1,z2,z3,z4,z877,z8]),(0,[z1,z2,z3,z4,z878,z8]),(0,[z511,z1,z3,z117,z5,z8]),(1,[z1,z3,z4,z718,z5])],[(0,[z1,z2,z3,z4,z772,z8]),(0,[z71,z1,z804,z4,z5,z8]),(0,[z879,z2,z3,z4,z5,z8]),(0,[z1,z32,z3,z4,z806,z8]),(0,[z132,z1,z18,z2,z3,z106])],[(0,[z1,z2,z67,z821,z5,z8])]],
   [[(0,[z1,z2,z3,z4,z5,z880])],[(0,[z2,z3,z773,z4,z5,z8]),(0,[z71,z1,z338,z44,z5,z8]),(0,[z1,z3,z4,z806,z5,z8]),(0,[z1,z85,z442,z3,z4,z5])],[(0,[z133,z1,z2,z3,z4,z10]),(0,[z1,z2,z3,z4,z5,z881]),(0,[z167,z1,z168,z117,z5,z8])],[(0,[z1,z2,z3,z4,z579,z10]),(0,[z1,z2,z3,z4,z5,z882]),(0,[z65,z1,z2,z3,z4,z8]),(0,[z1,z2,z3,z4,z5,z883])],[(0,[z1,z121,z3,z291,z5,z8]),(0,[z1,z2,z3,z4,z884,z5]),(0,[z885,z1,z2,z3,z4,z5]),(0,[z1,z2,z500,z3,z4,z10]),(0,[z886,z2,z3,z4,z5,z8])],[(0,[z1,z2,z20,z4,z5,z10]),(0,[z1,z85,z3,z4,z98,z159]),(0,[z1,z251,z3,z67,z5,z8]),(1,[z1,z2,z3,z815,z8]),(0,[z1,z18,z2,z3,z4,z10])],[(0,[z1,z2,z3,z4,z5,z887]),(0,[z1,z2,z888,z4,z5,z8]),(0,[z1,z2,z3,z4,z454,z10]),(0,[z1,z270,z3,z4,z201,z10])],[(0,[z1,z2,z3,z4,z5,z889]),(0,[z1,z2,z4,z890,z5,z8]),(0,[z1,z2,z3,z323,z5,z40]),(0,[z1,z540,z2,z3,z4,z98]),(0,[z103,z1,z565,z3,z4,z5]),(0,[z1,z2,z3,z811,z69,z5])]],
   [[(0,[z1,z2,z4,z295,z403,z5]),(0,[z1,z2,z3,z4,z5,z891]),(0,[z1,z2,z3,z892,z4,z5]),(0,[z1,z2,z3,z4,z33,z10])],[(0,[z1,z146,z463,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z893]),(0,[z1,z3,z4,z806,z201,z8]),(0,[z1,z2,z3,z4,z5,z894]),(0,[z37,z1,z18,z2,z3,z4])],[(0,[z895,z1,z2,z3,z4,z8]),(0,[z1,z2,z3,z4,z5,z896]),(0,[z2,z3,z4,z772,z215,z8]),(0,[z1,z2,z3,z897,z5,z8]),(0,[z179,z2,z3,z4,z5,z353])],[(0,[z1,z2,z3,z898,z5,z8]),(0,[z1,z899,z3,z4,z5,z8]),(0,[z1,z104,z3,z123,z5,z8]),(0,[z1,z85,z3,z4,z33,z159]),(0,[z1,z900,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z901,z5])],[(0,[z1,z2,z3,z4,z5,z902]),(0,[z1,z2,z3,z903,z5,z8]),(0,[z1,z2,z3,z4,z5,z762]),(0,[z132,z1,z2,z3,z106,z8]),(0,[z630,z1,z2,z13,z4,z5])],[(0,[z1,z2,z3,z4,z5,z904]),(0,[z1,z905,z3,z4,z5,z8]),(0,[z1,z3,z760,z117,z5,z8]),(0,[z90,z1,z2,z3,z595,z5])],[(0,[z1,z2,z3,z4,z5,z906]),(0,[z65,z1,z18,z2,z3,z4]),(0,[z1,z2,z3,z4,z907,z8]),(0,[z1,z2,z3,z4,z5,z908])],[(0,[z417,z2,z3,z4,z5,z86]),(0,[z115,z1,z2,z4,z175,z5])]],
   [[(0,[z1,z2,z66,z67,z5,z10])],[(0,[z1,z2,z3,z4,z5,z909]),(0,[z1,z2,z910,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z911]),(0,[z1,z2,z3,z4,z912,z5])],[(0,[z1,z2,z3,z4,z589,z10]),(0,[z1,z2,z913,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z914])],[(0,[z1,z2,z3,z4,z915,z8]),(0,[z2,z172,z773,z4,z5,z8]),(0,[z37,z1,z2,z500,z3,z4]),(0,[z1,z2,z4,z49,z724,z8])],[(0,[z476,z2,z3,z4,z5,z86]),(0,[z1,z2,z3,z4,z5,z916]),(0,[z1,z2,z3,z52,z53,z138])],[(0,[z2,z3,z865,z111,z5,z8]),(0,[z2,z3,z4,z5,z86,z786]),(0,[z1,z2,z3,z4,z5,z917])],[(0,[z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z918,z5,z8]),(0,[z1,z2,z3,z4,z5,z919])],[(0,[z2,z3,z865,z4,z5,z8]),(0,[z128,z1,z3,z117,z5,z8]),(0,[z1,z2,z920,z3,z5,z8])]],
   [[(0,[z1,z2,z3,z4,z5,z723]),(0,[z1,z921,z3,z4,z5,z8]),(0,[z1,z2,z922,z4,z5,z8]),(0,[z96,z1,z2,z3,z4,z10]),(0,[z1,z3,z4,z9,z718,z5])],[(0,[z1,z2,z3,z923,z5,z8]),(0,[z1,z18,z274,z3,z4,z5]),(0,[z195,z2,z3,z4,z5,z204]),(0,[z670,z1,z2,z3,z143,z5]),(0,[z1,z2,z3,z924,z5,z8]),(0,[z29,z1,z2,z613,z5,z8]),(0,[z1,z2,z3,z925,z4,z5]),(0,[z141,z1,z2,z3,z362,z5])],[(0,[z1,z2,z3,z4,z5,z309]),(0,[z1,z2,z3,z926,z5,z8]),(0,[z37,z1,z2,z3,z4,z381]),(0,[z1,z2,z3,z927,z4,z5])],[(0,[z110,z18,z2,z3,z111,z5]),(0,[z1,z18,z799,z2,z3,z4])],[(0,[z1,z329,z2,z3,z4,z5]),(0,[z1,z2,z3,z41,z5,z63])],[(0,[z1,z2,z928,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z929])],[(0,[z1,z930,z2,z3,z4,z8]),(0,[z1,z931,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z215,z8]),(0,[z1,z2,z3,z4,z5,z932]),(0,[z1,z2,z3,z732,z5,z8]),(0,[z1,z251,z3,z26,z5,z8]),(0,[z1,z2,z3,z4,z611,z10])],[(0,[z171,z2,z172,z4,z5,z10]),(0,[z0,z2,z3,z92,z215,z8]),(0,[z1,z2,z3,z4,z127,z8]),(0,[z499,z2,z3,z4,z5,z204]),(0,[z1,z804,z44,z4,z5,z8]),(0,[z1,z3,z804,z4,z5,z8]),(0,[z1,z2,z3,z4,z933,z5]),(0,[z102,z1,z87,z2,z5,z8]),(0,[z1,z2,z3,z4,z724,z8])]],
   [[(0,[z1,z934,z2,z3,z4,z5]),(0,[z1,z146,z147,z4,z5,z10])],[(0,[z1,z2,z3,z4,z5,z935]),(0,[z1,z2,z3,z4,z936,z8]),(0,[z1,z87,z3,z130,z5,z8]),(0,[z68,z1,z2,z4,z49,z10])],[(0,[z1,z2,z3,z4,z937,z8]),(0,[z2,z773,z254,z4,z5,z8]),(0,[z1,z274,z3,z291,z5,z8]),(0,[z1,z18,z32,z3,z4,z201]),(0,[z1,z938,z3,z4,z5,z8])],[(1,[z1,z121,z3,z4,z10]),(0,[z1,z2,z3,z113,z5,z10]),(0,[z1,z2,z3,z939,z5,z8]),(0,[z1,z2,z3,z347,z4,z5]),(0,[z1,z146,z251,z4,z5,z8])],[(0,[z1,z2,z940,z4,z5,z8]),(0,[z1,z2,z3,z941,z4,z8]),(0,[z24,z2,z3,z4,z23,z8]),(0,[z1,z32,z3,z4,z201,z8]),(0,[z132,z1,z2,z3,z815,z8])],[(0,[z1,z85,z2,z3,z4,z127]),(0,[z1,z251,z66,z4,z5,z8])],[(0,[z1,z942,z2,z3,z4,z5]),(1,[z2,z3,z865,z5,z8]),(0,[z1,z2,z251,z26,z5,z8]),(0,[z1,z2,z3,z4,z105,z5])],[(0,[z166,z2,z3,z4,z5,z86]),(0,[z1,z2,z613,z4,z5,z10]),(0,[z1,z3,z4,z943,z5,z8])]],
   [[(0,[z1,z2,z3,z4,z5,z944]),(0,[z1,z2,z3,z291,z5,z381]),(0,[z1,z2,z3,z4,z5,z945])],[(0,[z1,z2,z946,z4,z5,z8]),(0,[z1,z2,z4,z403,z5,z10]),(0,[z947,z1,z2,z4,z5,z8])],[(0,[z1,z18,z2,z20,z4,z5]),(0,[z1,z948,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z949]),(0,[z1,z2,z3,z950,z5,z8]),(0,[z1,z2,z185,z4,z5,z8]),(0,[z16,z2,z3,z4,z5,z204]),(0,[z1,z2,z3,z4,z951,z5])],[(0,[z24,z1,z2,z3,z4,z10]),(0,[z1,z2,z185,z92,z5,z8]),(0,[z1,z2,z3,z4,z381,z10]),(0,[z558,z2,z3,z4,z5,z86]),(0,[z1,z2,z3,z338,z5,z8]),(0,[z1,z952,z2,z3,z4,z5]),(0,[z1,z2,z3,z811,z5,z40])],[(0,[z1,z2,z3,z4,z5,z953]),(0,[z1,z954,z3,z4,z5,z8]),(0,[z24,z2,z3,z4,z353,z8]),(0,[z1,z85,z3,z4,z5,z107]),(0,[z955,z2,z3,z4,z5,z8])],[(0,[z1,z2,z613,z117,z5,z8]),(0,[z1,z2,z3,z69,z4,z98])],[(0,[z1,z2,z3,z4,z5,z956]),(0,[z1,z2,z3,z399,z53,z8]),(0,[z1,z2,z3,z4,z5,z957]),(0,[z167,z1,z3,z117,z5,z8])]],
   [[(0,[z1,z2,z3,z4,z646,z10]),(0,[z1,z152,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z649,z10]),(0,[z1,z2,z3,z815,z4,z8])],[(0,[z182,z2,z254,z4,z5,z10]),(0,[z1,z958,z3,z4,z5,z8]),(0,[z1,z2,z20,z291,z5,z8]),(0,[z102,z1,z2,z216,z5,z8]),(0,[z128,z1,z2,z26,z5,z8]),(0,[z167,z1,z18,z3,z117,z5]),(0,[z1,z2,z3,z4,z959,z5]),(0,[z141,z1,z2,z3,z143,z5]),(1,[z1,z799,z2,z3,z4])],[(0,[z22,z99,z3,z4,z5,z8]),(0,[z1,z2,z960,z4,z5,z8]),(0,[z1,z2,z414,z4,z192,z8]),(0,[z961,z1,z2,z3,z4,z5]),(0,[z167,z228,z1,z3,z117,z5]),(0,[z1,z2,z821,z26,z5,z8])],[(0,[z1,z2,z3,z4,z5,z962]),(0,[z0,z2,z185,z4,z215,z8]),(0,[z128,z1,z2,z3,z5,z10]),(0,[z1,z2,z3,z4,z5,z963]),(0,[z1,z2,z50,z439,z4,z5])],[(0,[z1,z2,z3,z4,z964,z8]),(1,[z2,z773,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z386]),(0,[z1,z2,z3,z399,z4,z10]),(1,[z2,z3,z4,z772,z8]),(0,[z1,z18,z2,z66,z67,z5])],[(0,[z1,z2,z3,z4,z127,z40]),(0,[z1,z2,z67,z216,z5,z8]),(0,[z29,z1,z87,z146,z5,z8]),(0,[z1,z270,z3,z4,z5,z159]),(0,[z1,z715,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z965]),(0,[z1,z2,z3,z4,z5,z332]),(0,[z1,z2,z3,z4,z5,z390]),(0,[z1,z3,z4,z287,z201,z10])],[(0,[z1,z2,z3,z966,z5,z8]),(0,[z1,z2,z3,z347,z338,z5]),(0,[z1,z2,z3,z4,z967,z8]),(0,[z857,z18,z2,z3,z4,z5])]],
   [[(0,[z1,z2,z3,z4,z968,z8]),(0,[z1,z2,z3,z4,z969,z8]),(0,[z970,z1,z2,z3,z5,z8]),(0,[z971,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z98,z8])],[(0,[z1,z972,z3,z4,z5,z8]),(0,[z1,z785,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z127,z51])],[(0,[z1,z2,z3,z973,z5,z8]),(0,[z166,z2,z3,z4,z5,z786]),(0,[z102,z1,z251,z4,z5,z8]),(0,[z1,z2,z500,z3,z4,z33])],[(0,[z1,z577,z2,z3,z4,z10]),(0,[z1,z2,z3,z4,z5,z974]),(0,[z1,z2,z3,z4,z295,z5]),(0,[z1,z18,z2,z3,z4,z33]),(0,[z1,z85,z3,z4,z431,z5])],[(0,[z1,z2,z3,z4,z975,z5]),(0,[z1,z99,z3,z4,z201,z10]),(0,[z1,z2,z3,z976,z4,z5]),(0,[z1,z2,z3,z528,z4,z5])],[(0,[z1,z147,z804,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z977]),(0,[z0,z1,z274,z3,z4,z10]),(0,[z0,z35,z2,z3,z4,z8])],[(0,[z1,z2,z3,z216,z5,z10]),(0,[z1,z2,z3,z4,z5,z138])]],
   [[(0,[z1,z2,z3,z4,z5,z978]),(0,[z1,z2,z3,z4,z5,z979])],[(0,[z1,z2,z3,z980,z5,z8]),(0,[z1,z2,z3,z981,z4,z5]),(0,[z198,z494,z2,z3,z4,z5]),(0,[z197,z2,z3,z4,z5,z86]),(0,[z1,z251,z3,z4,z5,z10])],[(0,[z982,z2,z3,z4,z5,z8])],[(0,[z983,z1,z2,z3,z4,z5]),(0,[z1,z2,z984,z4,z5,z8]),(0,[z1,z3,z4,z17,z201,z10]),(0,[z1,z799,z2,z3,z4,z292]),(0,[z1,z2,z774,z4,z5,z10])],[(0,[z1,z2,z761,z3,z4,z5]),(0,[z1,z2,z3,z69,z5,z40])],[(0,[z24,z2,z3,z4,z772,z8]),(0,[z1,z985,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z284])],[(0,[z1,z2,z3,z986,z4,z5]),(0,[z1,z987,z2,z3,z4,z5]),(0,[z1,z2,z66,z231,z5,z8])],[(0,[z1,z2,z988,z4,z5,z8])]],
   [[(1,[z1,z2,z821,z5,z8])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z989,z5,z8]),(0,[z1,z2,z3,z4,z990,z5])],[(0,[z1,z2,z3,z92,z5,z6]),(0,[z1,z2,z3,z69,z595,z5])],[(0,[z171,z2,z773,z4,z5,z8]),(0,[z2,z3,z4,z5,z772,z8]),(0,[z991,z2,z3,z4,z5,z8]),(0,[z1,z2,z50,z502,z4,z5])],[(0,[z1,z2,z3,z992,z4,z5]),(0,[z1,z2,z66,z239,z5,z8])],[(0,[z1,z2,z3,z4,z263,z10]),(0,[z1,z2,z3,z4,z401,z10]),(1,[z1,z2,z3,z811,z5])],[(0,[z2,z728,z3,z4,z5,z8]),(0,[z1,z18,z2,z3,z113,z5]),(0,[z993,z1,z3,z4,z5,z8])],[(0,[z0,z1,z2,z20,z4,z10]),(0,[z994,z1,z2,z3,z4,z5]),(0,[z118,z1,z3,z4,z287,z10]),(0,[z1,z2,z3,z4,z60,z10])]],
   [[(0,[z404,z2,z3,z230,z5,z8]),(0,[z1,z2,z3,z291,z5,z10]),(0,[z1,z2,z3,z4,z5,z995]),(0,[z1,z2,z996,z3,z4,z5]),(0,[z132,z1,z2,z3,z106,z10]),(0,[z1,z18,z2,z3,z4,z536]),(0,[z1,z2,z442,z3,z4,z10])],[(0,[z1,z121,z3,z4,z5,z8]),(0,[z0,z2,z3,z4,z215,z6]),(0,[z609,z1,z44,z4,z5,z8]),(0,[z1,z2,z3,z4,z389,z10]),(0,[z1,z2,z136,z4,z192,z10])],[(0,[z94,z19,z3,z4,z5,z10]),(0,[z71,z1,z251,z4,z5,z8]),(0,[z1,z2,z3,z997,z5,z8]),(0,[z1,z2,z50,z4,z5,z51]),(0,[z886,z18,z2,z3,z4,z5])],[(0,[z1,z2,z3,z998,z5,z8]),(0,[z1,z2,z3,z4,z999,z5]),(0,[z1,z2,z4,z724,z5,z8])],[(0,[z1,z2,z3,z4,z696,z10]),(0,[z118,z1,z3,z4,z579,z8]),(0,[z1,z1000,z3,z4,z5,z8]),(0,[z237,z2,z172,z4,z5,z8]),(0,[z166,z1,z2,z3,z4,z127])],[(0,[z1,z2,z3,z4,z5,z1001]),(0,[z1,z2,z3,z4,z5,z1002]),(0,[z1003,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1004]),(0,[z1,z270,z3,z4,z5,z31])],[(0,[z0,z1,z2,z3,z4,z313]),(0,[z991,z18,z2,z3,z4,z5])],[(0,[z1005,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z98,z86]),(0,[z128,z1,z251,z3,z5,z8]),(0,[z1006,z2,z3,z4,z5,z8]),(0,[z2,z3,z4,z5,z1007,z8]),(0,[z1,z2,z3,z815,z5,z8])]],
   [[(0,[z1,z2,z3,z4,z70,z10]),(0,[z1,z2,z3,z4,z5,z1008]),(0,[z37,z1,z799,z2,z3,z4])],[(0,[z1,z1009,z2,z3,z4,z5]),(0,[z182,z2,z773,z4,z5,z8]),(0,[z1,z2,z3,z4,z1010,z5]),(0,[z0,z121,z3,z4,z215,z8]),(0,[z102,z1,z2,z4,z5,z10]),(0,[z1,z2,z3,z4,z5,z1011])],[(0,[z1,z2,z3,z92,z5,z8]),(0,[z1,z2,z3,z4,z5,z1012]),(0,[z1,z2,z1013,z3,z5,z8]),(0,[z1,z2,z50,z3,z4,z98])],[(0,[z1,z2,z3,z4,z5,z1014]),(0,[z1,z2,z3,z1015,z4,z5]),(0,[z115,z1,z2,z375,z4,z5]),(0,[z1,z2,z3,z4,z5,z1016])],[(0,[z1,z3,z44,z216,z5,z8]),(0,[z1,z2,z1017,z3,z4,z5])],[(0,[z1,z2,z3,z4,z308,z10])],[(0,[z1,z2,z3,z4,z5,z1018]),(0,[z1,z2,z185,z4,z5,z6]),(0,[z1,z18,z87,z3,z123,z5]),(0,[z1,z2,z3,z4,z5,z1019]),(0,[z1,z2,z3,z106,z815,z8])],[(0,[z1,z508,z3,z4,z201,z8]),(0,[z1,z2,z3,z4,z5,z1020]),(0,[z1,z2,z3,z1021,z5,z8]),(0,[z1,z2,z3,z1022,z4,z5]),(0,[z1,z2,z3,z1023,z5,z8]),(0,[z228,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z1024,z8]),(0,[z1,z2,z4,z724,z192,z8])]],
   [[(0,[z1025,z1,z2,z4,z5,z8]),(0,[z1,z2,z3,z4,z1026,z8]),(0,[z1,z2,z1027,z3,z4,z5])],[(0,[z485,z2,z3,z230,z5,z8]),(0,[z1,z596,z2,z3,z4,z10])],[(0,[z65,z1,z2,z3,z4,z381]),(0,[z71,z1,z44,z113,z5,z8]),(0,[z1,z2,z3,z4,z5,z1028])],[(0,[z1,z2,z3,z1029,z5,z8]),(0,[z29,z1,z2,z216,z5,z8]),(0,[z71,z1,z44,z4,z5,z10]),(0,[z165,z1,z3,z4,z17,z5])],[(0,[z1,z18,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1030]),(0,[z1,z1031,z3,z4,z5,z8]),(0,[z1,z2,z3,z1032,z5,z8]),(0,[z102,z1,z18,z2,z4,z5]),(0,[z1,z2,z3,z4,z5,z1033])],[(0,[z22,z99,z3,z4,z5,z537]),(0,[z1,z2,z414,z3,z4,z10]),(0,[z102,z228,z1,z2,z4,z5]),(0,[z1,z2,z3,z1034,z4,z5])],[(0,[z1,z121,z185,z4,z5,z8]),(0,[z1,z85,z3,z82,z4,z5])],[(0,[z1,z2,z3,z1035,z5,z8]),(0,[z1,z2,z3,z1036,z5,z8]),(0,[z1,z540,z2,z3,z4,z10]),(0,[z1,z1037,z3,z4,z5,z8])]],
   [[(0,[z1038,z2,z3,z4,z5,z8]),(0,[z1,z87,z3,z123,z5,z8]),(0,[z29,z1,z2,z26,z5,z8])],[(0,[z1,z2,z3,z4,z196,z5])],[(0,[z1,z2,z3,z4,z151,z10]),(0,[z1,z18,z146,z147,z4,z5]),(0,[z771,z2,z3,z4,z5,z8]),(0,[z132,z1,z2,z3,z106,z546])],[(0,[z1,z2,z3,z1039,z5,z8]),(0,[z1,z2,z3,z1040,z4,z5]),(0,[z110,z2,z3,z111,z5,z10]),(0,[z228,z1,z2,z4,z403,z5]),(0,[z1,z2,z3,z4,z1041,z8]),(0,[z1,z2,z3,z1042,z4,z5]),(0,[z1,z799,z2,z3,z4,z10])],[(0,[z1,z2,z3,z4,z1043,z8]),(0,[z1,z18,z121,z3,z4,z5])],[(0,[z1,z2,z1044,z4,z5,z8]),(0,[z1,z3,z4,z846,z5,z10])],[(0,[z1,z19,z3,z4,z201,z10]),(0,[z1,z2,z804,z4,z5,z8]),(0,[z1045,z1,z2,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z530])],[(0,[z1,z274,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z1046,z8]),(0,[z167,z1,z251,z3,z5,z8]),(0,[z1,z2,z3,z815,z53,z8]),(0,[z1,z2,z3,z4,z140,z10])]],
   [[(0,[z1,z2,z3,z1047,z5,z8]),(0,[z1,z274,z3,z92,z5,z8]),(1,[z1,z44,z216,z5,z8]),(0,[z1,z2,z3,z4,z1048,z8]),(0,[z1,z2,z168,z4,z5,z10]),(0,[z167,z102,z1,z2,z5,z8]),(0,[z1,z18,z2,z4,z403,z5]),(0,[z29,z1,z2,z821,z5,z8])],[(0,[z1,z2,z3,z4,z1049,z8]),(0,[z1,z2,z3,z4,z1050,z8]),(0,[z1,z2,z1051,z4,z5,z8])],[(0,[z1,z2,z3,z4,z678,z10]),(0,[z1,z2,z3,z52,z53,z10])],[(0,[z1052,z2,z3,z4,z5,z8]),(0,[z1,z251,z4,z26,z5,z8])],[(0,[z1,z2,z4,z1053,z5,z8]),(0,[z1,z2,z3,z4,z5,z546])],[(0,[z1,z2,z3,z4,z5,z381]),(0,[z103,z1,z3,z4,z17,z5])],[(0,[z1,z2,z3,z4,z175,z127]),(1,[z1,z3,z760,z5,z8]),(0,[z1054,z1,z2,z3,z4,z5])],[(0,[z0,z274,z3,z4,z215,z8]),(0,[z1,z18,z2,z136,z4,z192]),(0,[z1,z18,z2,z62,z3,z4])]],
   [[(0,[z1,z2,z1055,z4,z5,z8]),(0,[z1,z2,z1056,z4,z5,z8]),(0,[z24,z2,z3,z4,z23,z313]),(0,[z2,z3,z4,z5,z786,z8]),(0,[z1,z18,z2,z3,z338,z5]),(0,[z115,z1,z2,z4,z720,z5])],[(0,[z1,z2,z3,z4,z5,z1057]),(0,[z2,z3,z230,z865,z5,z8]),(0,[z1,z2,z3,z1058,z5,z8]),(0,[z141,z1,z2,z3,z811,z5])],[(0,[z1,z1059,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z1060,z5]),(0,[z1061,z1,z2,z3,z4,z5]),(1,[z1,z3,z4,z806,z8])],[(0,[z166,z2,z3,z4,z5,z353]),(0,[z1,z2,z3,z4,z718,z5])],[(0,[z1,z2,z3,z1062,z5,z8]),(0,[z1,z2,z3,z4,z5,z1063]),(0,[z1,z2,z3,z4,z762,z10]),(0,[z103,z1,z2,z3,z4,z127]),(0,[z1,z2,z3,z4,z1064,z5])],[(0,[z171,z18,z2,z172,z4,z5]),(0,[z110,z2,z3,z865,z5,z8]),(0,[z0,z2,z3,z4,z215,z381]),(0,[z1,z2,z3,z4,z5,z14]),(0,[z1,z2,z213,z4,z5,z51]),(0,[z1,z2,z3,z143,z811,z5])],[(0,[z182,z2,z254,z4,z5,z183]),(0,[z1,z2,z20,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1065]),(0,[z1,z2,z3,z321,z4,z10]),(0,[z71,z1,z44,z216,z5,z8]),(0,[z809,z1,z251,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z1066]),(0,[z1,z18,z2,z3,z291,z5]),(0,[z1,z44,z4,z216,z5,z8]),(0,[z1,z81,z147,z4,z5,z8]),(0,[z1,z613,z4,z117,z5,z8]),(0,[z167,z1,z3,z760,z5,z8]),(0,[z1,z270,z3,z4,z201,z8]),(0,[z1,z18,z2,z3,z556,z4])]],
   [[(0,[z94,z18,z19,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1067])],[(0,[z1,z7,z2,z3,z4,z10]),(0,[z1,z2,z3,z4,z33,z8]),(0,[z1068,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z1069,z8]),(0,[z1,z2,z3,z1070,z4,z8]),(0,[z1,z2,z1071,z3,z4,z5]),(0,[z1,z1072,z2,z3,z4,z8]),(0,[z1,z18,z2,z3,z4,z127]),(0,[z71,z45,z1,z44,z4,z5]),(0,[z1073,z1,z2,z3,z5,z8]),(0,[z1,z146,z67,z117,z5,z8]),(0,[z1,z2,z3,z821,z5,z8])],[(0,[z1,z2,z3,z4,z5,z1074]),(0,[z1,z2,z3,z4,z1075,z8]),(0,[z1,z2,z3,z4,z232,z10])],[(0,[z1,z1076,z2,z3,z4,z8]),(0,[z1,z121,z3,z4,z5,z6]),(0,[z1,z274,z185,z4,z5,z8]),(0,[z1,z87,z66,z44,z5,z8])],[(0,[z1,z2,z3,z4,z201,z14]),(0,[z1077,z2,z3,z4,z5,z8]),(0,[z511,z29,z1,z2,z5,z8]),(0,[z1,z2,z4,z720,z5,z8])],[(0,[z0,z2,z20,z4,z215,z8]),(0,[z1,z2,z3,z1078,z5,z8])],[(0,[z1,z2,z3,z1079,z4,z5]),(0,[z1,z1080,z3,z4,z5,z8]),(1,[z1,z2,z4,z720,z5]),(0,[z1,z2,z3,z4,z292,z10])]],
   [[(0,[z1,z2,z3,z4,z5,z1081]),(0,[z1,z2,z3,z4,z5,z1082]),(0,[z128,z1,z18,z2,z3,z5]),(0,[z1,z2,z3,z4,z9,z98])],[(0,[z0,z1,z2,z3,z4,z10]),(0,[z1,z3,z4,z287,z806,z8]),(0,[z1,z2,z66,z67,z5,z8])],[(0,[z1,z2,z1083,z3,z4,z8]),(0,[z1,z2,z3,z4,z5,z1084]),(0,[z1,z2,z185,z4,z5,z381]),(0,[z65,z1,z2,z3,z4,z10]),(0,[z1,z85,z3,z4,z718,z5])],[(0,[z1,z2,z3,z1085,z5,z8]),(0,[z1,z2,z3,z4,z5,z786]),(0,[z1,z32,z3,z4,z201,z14])],[(0,[z1,z2,z3,z4,z5,z537]),(0,[z576,z2,z3,z111,z5,z8]),(0,[z166,z2,z3,z4,z86,z127]),(0,[z1,z1086,z3,z4,z5,z8]),(0,[z1087,z1,z2,z3,z4,z5])],[],[(0,[z1,z2,z3,z4,z1088,z5]),(0,[z1,z2,z1089,z4,z5,z8]),(0,[z1,z2,z3,z4,z98,z204]),(0,[z1,z2,z4,z890,z5,z10])],[(0,[z1,z2,z3,z1090,z5,z8])]],
   [[(0,[z1,z1091,z2,z3,z4,z5]),(0,[z99,z728,z3,z4,z5,z8]),(0,[z1,z1092,z3,z4,z5,z8]),(0,[z1,z2,z3,z1093,z4,z5]),(0,[z1077,z18,z2,z3,z4,z5]),(0,[z982,z18,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z1094]),(0,[z404,z2,z3,z865,z5,z8]),(0,[z0,z1,z121,z3,z4,z10]),(0,[z128,z45,z1,z2,z3,z5]),(0,[z1,z2,z3,z4,z190,z10]),(0,[z1095,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z897,z5,z10])],[(0,[z1,z1096,z3,z4,z5,z8]),(0,[z404,z18,z2,z3,z230,z5]),(0,[z1,z2,z1097,z4,z5,z8]),(0,[z1,z2,z4,z1098,z5,z8]),(0,[z1,z2,z3,z811,z4,z5])],[(0,[z1,z2,z3,z4,z5,z1099]),(0,[z1,z2,z3,z4,z5,z1100])],[(0,[z1,z2,z1101,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1102]),(0,[z141,z1,z2,z3,z305,z5]),(0,[z1,z18,z2,z3,z4,z636])],[(0,[z1,z2,z3,z4,z1103,z5]),(0,[z1,z121,z3,z92,z5,z8])],[(0,[z1,z2,z3,z4,z5,z1104]),(1,[z1,z2,z3,z4,z723]),(0,[z1,z2,z66,z613,z5,z8]),(0,[z1105,z2,z3,z4,z5,z8])],[(0,[z1,z508,z2,z3,z4,z10]),(0,[z895,z1,z2,z3,z4,z56]),(0,[z1,z2,z1106,z3,z4,z5])]]]

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
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 531).take 538) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1069).take 99) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1168)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [531, 538, 99] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 113).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 113).take 124).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 237).take 19).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [113, 124, 19] = true :=
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

end PEqualNP.Outside.L_meta_43926

theorem PEqualNP.Outside.L_meta_43926 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813000 * 2 ^ 32 + 4276791424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813000 * 2 ^ 32 + 4276791424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_43926.solve