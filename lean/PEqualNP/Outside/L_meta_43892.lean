import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_43892

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
  Nat.testBit (4276809450 * 2 ^ 32 + 4276799616) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x00010856021586d4#64 ++ 0x400004215808561b#64 ++ 0x013b18fe063f8fdf#64 ++ 0xbc04ec63f818fe3f#64 : BitVec 256),
   (0x4250633018cc3b42#64 ++ 0x8109418cc06330ed#64 ++ 0xc6d4e73039ccffff#64 ++ 0x7f1b539cc0e733ff#64 : BitVec 256),
   (0x18a705c2c170d19b#64 ++ 0x04629c170b05c346#64 ++ 0x78e707c3c1f0f1f6#64 ++ 0xede39c1f0f07c3c7#64 : BitVec 256),
   (0xad07b8036e00ec1c#64 ++ 0x02b41ee00db803b0#64 ++ 0xbf07f803fe00fe3d#64 ++ 0xf2fc1fe00ff803f8#64 : BitVec 256),
   (0x37f80001b5aa0020#64 ++ 0x00dfe00006d6a800#64 ++ 0x3ff80003ffff0033#64 ++ 0xf4ffe0000ffffc00#64 : BitVec 256),
   (0x3ffed6a800000000#64 ++ 0x08fffb5aa0000000#64 ++ 0xfffffffc0000000f#64 ++ 0xebfffffff0000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [2, 3]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [9, 4]⟩, ⟨.and, [7, 11]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [10, 13]⟩, ⟨.or, [14, 12]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x00010856021586d4 0x400004215808561b 0x013b18fe063f8fdf 0xbc04ec63f818fe3f

def z1 : W := mkw 0x18a705c2c170d19b 0x04629c170b05c346 0x78e707c3c1f0f1f6 0xede39c1f0f07c3c7

def z2 : W := mkw 0x18a70dd6c375d7df 0x44629c375b0dd75f 0x78e707c3c7fffff6 0xfde39c1f0f1fffff

def z3 : W := mkw 0x37f80001b5aa0020 0x00dfe00006d6a800 0x3ff80003ffff0033 0xf4ffe0000ffffc00

def z4 : W := mkw 0x3ffed6a800000000 0x08fffb5aa0000000 0xfffffffc0000000f 0xebfffffff0000000

def z5 : W := mkw 0x4250633018cc3b42 0x8109418cc06330ed 0xc6d4e73039ccffff 0x7f1b539cc0e733ff

def z6 : W := mkw 0xad07b8036e00ec1c 0x02b41ee00db803b0 0xbf07f803fe00fe3d 0xf2fc1fe00ff803f8

def z7 : W := mkw 0x18a60580c160510b 0x0462981603058144 0x78c40701c1c0f1f6 0x6de3101c070703c7

def z8 : W := mkw 0x0001080202008414 0x0000042008080210 0x0103180206008e1d 0xb0040c6008180238

def z9 : W := mkw 0x3ffed6a9b5aa0020 0x08fffb5aa6d6a800 0xffffffffffff003f 0xfffffffffffffc00

def z10 : W := mkw 0x52f0633099ec3b42 0x814bc18cc267b0ed 0xfef4e733f9fcffff 0xfffbd39ccfe7f3ff

def z11 : W := mkw 0x080705c24050d19b 0x04201c1709014346 0x400707c00000f1c4 0x09001c1f000003c7

def z12 : W := mkw 0x27580001348a0020 0x009d600004d22800 0x071800003e0f0001 0x101c600000f83c00

def z13 : W := mkw 0x35a80001a5220020 0x00d6a00006948800 0x39280003c6330000 0x80e4a0000f18cc00

def z14 : W := mkw 0x37f84221b5aa0020 0x00dfe10886d6a800 0xfffce733ffff003f 0xfffff39ccffffc00

def z15 : W := mkw 0x0001004200108090 0x0000040108004202 0x002300c2003081d6 0xac008c030800c207

def z16 : W := mkw 0xad07b8436e10ec9c 0x02b41ee10db843b2 0xbf27f8c3fe30ffff 0xfefc9fe30ff8c3ff

def z17 : W := mkw 0xad07b8036e00ec1c 0x02b41ee00db803b0 0xbf3ff803fe3ffe3f 0xf6fcffe00ff8fff8

def z18 : W := mkw 0x27580815368f0664 0x409d602054da3c19 0x0718183c3e0f0e09 0x101c6060f0f83c38

def z19 : W := mkw 0x3fffdefe021586d4 0x48ffff7bf808561b 0xfffffffe063f8fdf 0xfffffffff818fe3f

def z20 : W := mkw 0x0806d6a800000000 0x08201b5aa0000000 0xc007fffc0000000c 0x0b001ffff0000000

def z21 : W := mkw 0x4250632018c83902 0x8109418c806320e4 0xc6c4e70039c07020 0x431b139c00e701c0

def z22 : W := mkw 0x7ffef7b818cc3b42 0x89fffbdee06330ed 0xfffffffc39ccffff 0xfffffffff0e733ff

def z23 : W := mkw 0x18a70582c160d11b 0x04629c160b058344 0x78c70703c1c0f034 0xe1e31c1c0f0703c0

def z24 : W := mkw 0xa500b8012e002c04 0x029402e004b800b0 0xbf00f803fe000e39 0xf2fc03e00ff80038

def z25 : W := mkw 0x0250000000000000 0x0009400000000000 0x06d0000000000003 0x601b400000000000

def z26 : W := mkw 0x4000633008443b42 0x8100018cc02110ed 0xc004e7300000ffcc 0x0b00139cc00003ff

def z27 : W := mkw 0x4000433000441342 0x8100010cc001104d 0x40000730000001c0 0x0900001cc0000007

def z28 : W := mkw 0x25000001b5aa0020 0x0094000006d6a800 0x3f000003ffff0031 0xf4fc00000ffffc00

def z29 : W := mkw 0x12f846fc001502c0 0x484be11bf000540b 0x40f807fc003f01c2 0x0d03e01ff000fc07

def z30 : W := mkw 0x18a704c2c130c099 0x04629c130b04c302 0x382300c3c0300000 0x80e08c030f00c000

def z31 : W := mkw 0x42506230188c2a40 0x81094188c06230a9 0x8610e030380c0e09 0x12184380c0e03038

def z32 : W := mkw 0x10a0000081200000 0x0042800002048000 0x38e00003c1f00032 0xe4e380000f07c000

def z33 : W := mkw 0x3fff05c3f5fad1bb 0x04fffc170fd7eb46 0x7fff07c3fffff1f7 0xfdfffc1f0fffffc7

def z34 : W := mkw 0x0000000000000000 0x0000000000000000 0x40c4070000000006 0x6903101c00000000

def z35 : W := mkw 0x3fffd7eac170d19b 0x0cffff5fab05c346 0xffffffffc1f0f1ff 0xefffffffff07c3c7

def z36 : W := mkw 0x3ffed6a9b5aa0020 0x08fffb5aa6d6a800 0xfec4e701f9c00020 0x43fb139c07e70000

def z37 : W := mkw 0x3fffd6ea00108090 0x08ffff5ba8004202 0xfffffffe003081df 0xeffffffff800c207

def z38 : W := mkw 0x4250633018cc3b42 0x8109418cc06330ed 0x8610e03039ccfff9 0x16184380c0e733ff

def z39 : W := mkw 0x42506230188c2a40 0x81094188c06230a9 0x8614e030380cfe3d 0x72185380c0e033f8

def z40 : W := mkw 0x12f8000091aa0020 0x004be0000246a800 0x00f8000001ff0002 0x0403e0000007fc00

def z41 : W := mkw 0x3ffed6a891aa0020 0x08fffb5aa246a800 0xfffffffc01ff000f 0xeffffffff007fc00

def z42 : W := mkw 0x0000000000000000 0x0000000000000000 0x00380000003f0002 0x0400e0000000fc00

def z43 : W := mkw 0x12f846a800000000 0x084be11aa0000000 0x40c0070000000000 0x0103001c00000000

def z44 : W := mkw 0x0000001000040240 0x0000000040001009 0x00100030000c8fdf 0x3c004000c000323f

def z45 : W := mkw 0x42516b761addbfd6 0xc10945add86b76ff 0xc7fffffe3fffffff 0xff1ffffff8ffffff

def z46 : W := mkw 0x77f86331bdee3b62 0x81dfe18cc6f7b8ed 0xfffce733ffffffff 0xfffff39ccfffffff

def z47 : W := mkw 0x3daed6a800000000 0x08f6bb5aa0000000 0xf92ffffc0000000c 0x8be4bffff0000000

def z48 : W := mkw 0x3daf9cde021586d4 0x48f6be737808561b 0x393b18fe063f8fdf 0xbce4ec63f818fe3f

def z49 : W := mkw 0x18a70dd6c375d7df 0x44629c375b0dd75f 0x79ff1fffc7ffffff 0xfde7fc7fff1fffff

def z50 : W := mkw 0x0250000010880000 0x0009400000422000 0x06c0000039c00020 0x401b000000e70000

def z51 : W := mkw 0x3dae948800000000 0x08f6ba5220000000 0x392b18cc00000000 0x80e4ac6330000000

def z52 : W := mkw 0x4000211018cc3b42 0x81000084406330ed 0x0000000039ccfff0 0x1400000000e733ff

def z53 : W := mkw 0x800128576e15eedc 0x420004a15db857bb 0x013b18fffe3fffff 0xbc04ec63fff8ffff

def z54 : W := mkw 0x000005c000501183 0x0400001700014046 0x400007c0000001c0 0x0900001f00000007

def z55 : W := mkw 0x0806048000000000 0x0020181200000000 0x400707c000000004 0x09001c1f00000000

def z56 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z57 : W := mkw 0x1af705c2d1f8d19b 0x046bdc170b47e346 0x7ef707c3f9fcf1f7 0xfdfbdc1f0fe7f3c7

def z58 : W := mkw 0x0000000000000000 0x0000000000000000 0x01380002063f0013 0xb404e0000818fc00

def z59 : W := mkw 0x77f86331bdee3b62 0x81dfe18cc6f7b8ed 0xfed4e731f9ccffff 0x7ffb539cc7e733ff

def z60 : W := mkw 0x18a704c2c130c099 0x04629c130b04c302 0x382300c3c03081d6 0xace08c030f00c207

def z61 : W := mkw 0x675862313c8e2a60 0x819d6188c4f238a9 0x8718e0303e0f0e09 0x121c6380c0f83c38

def z62 : W := mkw 0x37f90857b7bf86f4 0x40dfe4215edefe1b 0x3ffb18ffffff8fff 0xfcffec63fffffe3f

def z63 : W := mkw 0x800128576e15eedc 0x420004a15db857bb 0x00000003fe3ffff0 0x140000000ff8ffff

def z64 : W := mkw 0x37f8000000000000 0x00dfe00000000000 0x3ff8000000000003 0xe0ffe00000000000

def z65 : W := mkw 0x25010857261586d4 0x409404215c98561b 0x3f3b18fffe3f8fff 0xfcfcec63fff8fe3f

def z66 : W := mkw 0x10a105c2c170d19b 0x044284170b05c346 0x40e007c3c1f0f1f2 0x0d03801f0f07c3c7

def z67 : W := mkw 0x0000000000000000 0x0000000000000000 0x002300c000000006 0xa8008c0300000000

def z68 : W := mkw 0x18a70dd6c375d7df 0x44629c375b0dd75f 0x78e71fffc1f0fffe 0xede39c7fff07c3ff

def z69 : W := mkw 0xad07b8036e00ec1c 0x02b41ee00db803b0 0xbe04e003fe00fe30 0x52f813800ff803f8

def z70 : W := mkw 0x3ffed6a800000000 0x08fffb5aa0000000 0xfec7fffc0000000c 0x4bfb1ffff0000000

def z71 : W := mkw 0x18a705c2c170d19b 0x04629c170b05c346 0x78c40703c1f0f1f0 0x45e3101c0f07c3c7

def z72 : W := mkw 0x00010856021586d4 0x400004215808561b 0x00000002063f8fd0 0x140000000818fe3f

def z73 : W := mkw 0x0001014200509192 0x0000040508014246 0x40e707c201f0f1f6 0xed039c1f0807c3c7

def z74 : W := mkw 0x0000200008002800 0x00000080002000a0 0x8604e0003800fe3d 0x7218138000e003f8

def z75 : W := mkw 0xad07b8576e15eedc 0x42b41ee15db857bb 0xbf3ff8fffe3fffff 0xfefcffe3fff8ffff

def z76 : W := mkw 0x00010142c170d19b 0x040004050b05c346 0x00000003c1f0f1f0 0x040000000f07c3c7

def z77 : W := mkw 0x2758d22800000000 0x089d6348a0000000 0x8718f83c00000009 0x021c63e0f0000000

def z78 : W := mkw 0x6758f33818cc3b42 0x899d63cce06330ed 0xc7dcff3c39ccffff 0x7f1f73fcf0e733ff

def z79 : W := mkw 0x77f86231bdae2a60 0x81dfe188c6f6b8a9 0xbff8e033ffff0e3b 0xf6ffe380cffffc38

def z80 : W := mkw 0x8807b8024a00ec1c 0x02201ee0092803b0 0x8007f8000000fe0c 0x02001fe0000003f8

def z81 : W := mkw 0xbfffb803ffaaec3c 0x02fffee00ffeabb0 0xbffff803fffffe3f 0xf6ffffe00ffffff8

def z82 : W := mkw 0x400129561addbfd6 0xc10004a5586b76ff 0x013b18fe3fffffff 0xbc04ec63f8ffffff

def z83 : W := mkw 0x18a705c2c170d19b 0x04629c170b05c346 0x78c707c1c1c0f1e4 0x49e31c1f070703c7

def z84 : W := mkw 0x18a60580c160510b 0x0462981603058144 0x78e40703c1f07032 0xe5e3901c0f07c1c0

def z85 : W := mkw 0x2d06900000000000 0x00b41a4000000000 0xbf3ff8fc0000000f 0xeafcffe3f0000000

def z86 : W := mkw 0x4000633018cc3b42 0x8100018cc06330ed 0xc004e73039ccfffc 0x1f00139cc0e733ff

def z87 : W := mkw 0x2d06900000000000 0x00b41a4000000000 0xbf07f8000000000d 0xe2fc1fe000000000

def z88 : W := mkw 0x0a56d6a800000000 0x08295b5aa0000000 0xc6d7fffc0000000f 0x6b1b5ffff0000000

def z89 : W := mkw 0x4250633018cc3b42 0x8109418cc06330ed 0xc7fce7323fffffff 0xff1ff39cc8ffffff

def z90 : W := mkw 0x77f86321bdea3922 0x81dfe18c86f7a8e4 0xfffce703ffff7033 0xf7fff39c0ffffdc0

def z91 : W := mkw 0x18a605c0c170518b 0x046298170305c146 0x78e407c1c1f071e2 0x4de3901f0707c1c7

def z92 : W := mkw 0x00010956025597d6 0x400004255809565f 0x41ff1ffe07ffffff 0xfd07fc7ff81fffff

def z93 : W := mkw 0x52f8433091ee1362 0x814be10cc247b84d 0x40f8073001ff01c2 0x0d03e01cc007fc07

def z94 : W := mkw 0x18a60580c160510b 0x0462981603058144 0x78c40701c1c07020 0x41e3101c070701c0

def z95 : W := mkw 0x37f80101b5ea1122 0x00dfe00406d7a844 0x7ffc0703fffff1f7 0xfdfff01c0fffffc7

def z96 : W := mkw 0x37f8422000000000 0x00dfe10880000000 0xfffce7300000000f 0xebfff39cc0000000

def z97 : W := mkw 0x02500001b5aa0020 0x0009400006d6a800 0x06d00003ffff0033 0x741b40000ffffc00

def z98 : W := mkw 0x12f846a800000000 0x084be11aa0000000 0x40f807fc00000002 0x0903e01ff0000000

def z99 : W := mkw 0x800128036e00ec1c 0x020004a00db803b0 0x00000003fe00fe30 0x100000000ff803f8

def z100 : W := mkw 0x0000081402050644 0x4000002050081419 0x0000183c00000e08 0x00000060f0000038

def z101 : W := mkw 0x080700024000c018 0x00201c0009000300 0x38070003c000f034 0xe0e01c000f0003c0

def z102 : W := mkw 0xbda7bdc3ef70fd9f 0x06f69ef70fbdc3f6 0xffe7ffc3fff0ffff 0xffff9fff0fffc3ff

def z103 : W := mkw 0x37f80001b5aa0020 0x00dfe00006d6a800 0x3ec00003ffff0030 0x54fb00000ffffc00

def z104 : W := mkw 0x18a6048000000000 0x0062981200000000 0x78e707c000000006 0xe9e39c1f00000000

def z105 : W := mkw 0x0806000040004008 0x0020180001000100 0x38040001c0007020 0x40e01000070001c0

def z106 : W := mkw 0x10a005c081701183 0x044280170205c046 0x40e007c001f001c2 0x0d03801f0007c007

def z107 : W := mkw 0xef56f3317ccc7b4a 0x83bd5bccc5f331ed 0xfed4e731f9ccffff 0x7ffb539cc7e733ff

def z108 : W := mkw 0x000046a800000000 0x0800011aa0000000 0x400007fc00000000 0x0900001ff0000000

def z109 : W := mkw 0x0250000010880000 0x0009400000422000 0x06d0000039cc0033 0x741b400000e73000

def z110 : W := mkw 0x27580001348a0020 0x009d600004d22800 0x073800023e3f0013 0xb41ce00008f8fc00

def z111 : W := mkw 0xad07b9036e40fd1e 0x02b41ee40db903f4 0xffc7ff03ffc0ffff 0xffff1ffc0fff03ff

def z112 : W := mkw 0x02500010108c0240 0x0009400040423009 0x06d0003039cc8fff 0x7c1b4000c0e7323f

def z113 : W := mkw 0x8000b8000a002c04 0x020002e0002800b0 0x8000f80000000e08 0x020003e000000038

def z114 : W := mkw 0x42516372d9fcfbdb 0x8509458dcb67f3ef 0xc6d4e733f9fcffff 0x7f1b539ccfe7f3ff

def z115 : W := mkw 0x10a0058081601103 0x0442801602058044 0x40c0070001c00000 0x0103001c00070000

def z116 : W := mkw 0x2f5ed6a800000000 0x08bd7b5aa0000000 0xc71ffffc0000000d 0x0b1c7ffff0000000

def z117 : W := mkw 0x00010856021586d4 0x400004215808561b 0x013b18fe063f0e09 0x9004ec63f818fc38

def z118 : W := mkw 0x00000001b5aa0020 0x0000000006d6a800 0x00000003ffff0030 0x140000000ffffc00

def z119 : W := mkw 0xad07feab6e00ec1c 0x0ab41ffaadb803b0 0xff07fffffe00fe3d 0xfbfc1ffffff803f8

def z120 : W := mkw 0xbdafb803ef22ec3c 0x02f6bee00fbc8bb0 0xbf2ff803fe33fe3d 0xf2fcbfe00ff8cff8

def z121 : W := mkw 0x1afed6a800000000 0x086bfb5aa0000000 0xc0fffffc0000000e 0x0b03fffff0000000

def z122 : W := mkw 0x00010856021586d4 0x400004215808561b 0x013b18fe063f01c2 0x8c04ec63f818fc07

def z123 : W := mkw 0x37f82001bdaa2820 0x00dfe08006f6a8a0 0xbffce003fffffe3f 0xf6fff3800ffffff8

def z124 : W := mkw 0xad0798036600c41c 0x02b41e600d980310 0x39031803c6000000 0x80e40c600f180000

def z125 : W := mkw 0x00000054001502c0 0x400000015000540b 0x000000fc000001c0 0x08000003f0000007

def z126 : W := mkw 0x675863313cce3b62 0x819d618cc4f338ed 0xc7dce7303fcfffff 0x7f1f739cc0ff3fff

def z127 : W := mkw 0xbfffffebef70fd9f 0x0effffffafbdc3f6 0xfffffffffff0ffff 0xffffffffffffc3ff

def z128 : W := mkw 0x3fffd7ebf5fad1bb 0x0cffff5fafd7eb46 0xfffffffffffff1ff 0xffffffffffffffc7

def z129 : W := mkw 0x0807defe021586d4 0x48201f7bf808561b 0xc13ffffe063f8fdf 0xbf04fffff818fe3f

def z130 : W := mkw 0x3ffed6a800000000 0x08fffb5aa0000000 0xfec4e70000000000 0x43fb139c00000000

def z131 : W := mkw 0x0000010000401102 0x0000000400010044 0x40c0070001c001c2 0x0d03001c00070007

def z132 : W := mkw 0x4a56f7b818cc3b42 0x89295bdee06330ed 0xc6d7fffc39ccffff 0x7f1b5ffff0e733ff

def z133 : W := mkw 0x00010856021586d4 0x400004215808561b 0x00100032063f8fdf 0x3c004000c818fe3f

def z134 : W := mkw 0xed07b9137eccff5e 0x83b41ee44dfb33fd 0xbf07f803ffccfffd 0xf6fc1fe00fff33ff

def z135 : W := mkw 0x0001084602118494 0x4000042118084612 0x012b18ce06330000 0x8004ac633818cc00

def z136 : W := mkw 0x18a70dc6c371d59f 0x44629c371b0dc756 0x79ef1fcfc7f3f1f6 0xede7bc7f3f1fcfc7

def z137 : W := mkw 0x4250433010cc1342 0x8109410cc043304d 0x40d0073001cc01c2 0x0d03401cc0073007

def z138 : W := mkw 0xad06b0016c006808 0x02b41ac005b001a0 0xbe04e001f8007020 0x42f8138007e001c0

def z139 : W := mkw 0x3fffd6aa4000c018 0x08ffff5aa9000300 0xffffffffc000f03f 0xebffffffff0003c0

def z140 : W := mkw 0x2500000124000000 0x0094000004900000 0x3f000003fe000031 0xf0fc00000ff80000

def z141 : W := mkw 0x0000081402050644 0x4000002050081419 0x0118183c060f0e09 0x10046060f0183c38

def z142 : W := mkw 0xa500b8012e002c04 0x029402e004b800b0 0x8700f8003e000e09 0x121c03e000f80038

def z143 : W := mkw 0x3fffdeffb7bf86f4 0x48ffff7bfedefe1b 0xffffffffffff8fff 0xfffffffffffffe3f

def z144 : W := mkw 0xed07fb336e44ff5e 0x83b41feccdb913fd 0xff07ff33fe00fffd 0xfbfc1ffccff803ff

def z145 : W := mkw 0x3ffed6fc001502c0 0x48fffb5bf000540b 0xfffffffc003f01cf 0xeffffffff000fc07

def z146 : W := mkw 0x0000010000401102 0x0000000400010044 0x40c4070001c0f1f6 0x6d03101c000703c7

def z147 : W := mkw 0xad07b8036e00ec1c 0x02b41ee00db803b0 0x39031803fe00fe30 0x90e40c600ff803f8

def z148 : W := mkw 0x10a8048800000000 0x0842a01220000000 0x002800cc00000000 0x0000a00330000000

def z149 : W := mkw 0x42514b7612dd97d6 0xc109452dd84b765f 0x41fb1ffe07ff8fdf 0xbd07ec7ff81ffe3f

def z150 : W := mkw 0x080705c24050d19b 0x04201c1709014346 0x402707c20030f1d6 0xad009c1f0800c3c7

def z151 : W := mkw 0x0001080202008414 0x0000042008080210 0x0103180206000000 0x80040c6008180000

def z152 : W := mkw 0x3ffe948800000000 0x08fffa5220000000 0x3ffb18cc00000003 0xe0ffec6330000000

def z153 : W := mkw 0x0250422000000000 0x0009410880000000 0xc6d4e7300000000f 0x6b1b539cc0000000

def z154 : W := mkw 0x2d06900124000000 0x00b41a4004900000 0xbf07f803fe00003d 0xf2fc1fe00ff80000

def z155 : W := mkw 0x3ffed6a924000000 0x08fffb5aa4900000 0xfffffffffe00003f 0xfbfffffffff80000

def z156 : W := mkw 0x18a70002c120c018 0x00629c000b048300 0x38e70003c1f0f036 0xe4e39c000f07c3c0

def z157 : W := mkw 0x0000001400050240 0x4000000050001409 0x0018003c000f0000 0x00006000f0003c00

def z158 : W := mkw 0x37f8000081200000 0x00dfe00002048000 0x3ff80003c1f00033 0xe4ffe0000f07c000

def z159 : W := mkw 0xbfffdeab6600c41c 0x0affff7aad980310 0xffffffffc600000f 0xebffffffff180000

def z160 : W := mkw 0x18a705c3f5fad1bb 0x04629c170fd7eb46 0x78e707c3fffff1f6 0xfde39c1f0fffffc7

def z161 : W := mkw 0x0000000000000000 0x0000000000000000 0x013b18fc0000000f 0xa804ec63f0000000

def z162 : W := mkw 0x37f80001b5aa0020 0x00dfe00006d6a800 0x3fd80001ffcf0021 0x50ff600007ff3c00

def z163 : W := mkw 0x080720024800e818 0x00201c80092003a0 0xbe07e003f800fe3d 0xf2f81f800fe003f8

def z164 : W := mkw 0x5af767f2d9fcfbdb 0x856bdd9fcb67f3ef 0xfef7e7f3f9fcffff 0xfffbdf9fcfe7f3ff

def z165 : W := mkw 0x37f80001b5aa0020 0x00dfe00006d6a800 0x3ed00001f9cc0033 0x74fb400007e73000

def z166 : W := mkw 0x00000054001502c0 0x400000015000540b 0x003800fc003f01c2 0x0c00e003f000fc07

def z167 : W := mkw 0x10a0048000000000 0x0042801200000000 0x40e007c000000002 0x0903801f00000000

def z168 : W := mkw 0xad07b8476e11ec9c 0x42b41ee11db847b2 0xbf2ff8cffe33fe3d 0xf2fcbfe33ff8cff8

def z169 : W := mkw 0xbfffbdc3fffafdbf 0x06fffef70fffebf6 0xffffffc3ffffffff 0xffffffff0fffffff

def z170 : W := mkw 0x12f846a891aa0020 0x084be11aa246a800 0x40f807fc01ff0002 0x0d03e01ff007fc00

def z171 : W := mkw 0x18a705c2c170d19b 0x04629c170b05c346 0x382300c3c1f0f1f0 0x84e08c030f07c3c7

def z172 : W := mkw 0x4250633018cc3b42 0x8109418cc06330ed 0xc6c4e73039c0ffec 0x4b1b139cc0e703ff

def z173 : W := mkw 0x250020012c002800 0x0094008004b000a0 0xbf04e003fe00fe3d 0xf2fc13800ff803f8

def z174 : W := mkw 0x37f80011b5ae0260 0x00dfe00046d6b809 0x3ff80033ffff8fff 0xfcffe000cffffe3f

def z175 : W := mkw 0x18a70dc2c370d59f 0x04629c370b0dc356 0x79e71fc3c7f0ffff 0xfde79c7f0f1fc3ff

def z176 : W := mkw 0x3ffed6a881200000 0x08fffb5aa2048000 0xffffffffc1f0003f 0xefffffffff07c000

def z177 : W := mkw 0xfff7fff3fffcffdf 0x87ffdfffcffff3ff 0xfff7fff3fffcffff 0xffffdfffcffff3ff

def z178 : W := mkw 0xbdaf9803e722c43c 0x02f6be600f9c8b10 0x392b1803c6330000 0x80e4ac600f18cc00

def z179 : W := mkw 0x00010856021586d4 0x400004215808561b 0x012b18ce063f8fd0 0x9404ac633818fe3f

def z180 : W := mkw 0x3daf04c3e532c0b9 0x04f6bc130f94cb02 0x392b00c3c6330000 0x80e4ac030f18cc00

def z181 : W := mkw 0x3ffe0481b5aa0020 0x00fff81206d6a800 0x7fff07c3ffff0037 0xfdfffc1f0ffffc00

def z182 : W := mkw 0x3dae948800000000 0x08f6ba5220000000 0x79ef1fcc00000006 0xe9e7bc7f30000000

def z183 : W := mkw 0xbffffeabffaaec3c 0x0afffffaaffeabb0 0xfffffffffffffe3f 0xfffffffffffffff8

def z184 : W := mkw 0x18a704c2c130c099 0x04629c130b04c302 0x78e707c3c0300006 0xe9e39c1f0f00c000

def z185 : W := mkw 0x4250633018cc3b42 0x8109418cc06330ed 0x40d0073039ccfff2 0x1d03401cc0e733ff

def z186 : W := mkw 0xef57fb337eccff5e 0x83bd5feccdfb33fd 0xffd7ff33ffccffff 0xffff5ffccfff33ff

def z187 : W := mkw 0x37f8000000000000 0x00dfe00000000000 0x3ec0000000000000 0x40fb000000000000

def z188 : W := mkw 0x4250632018c83902 0x8109418c806320e4 0xc6c4e70039c0fe3d 0x731b139c00e703f8

def z189 : W := mkw 0x10a0000081200000 0x0042800002048000 0x38200003c0300000 0x80e080000f00c000

def z190 : W := mkw 0x3daf95cac170d19b 0x0cf6be572b05c346 0x79ef1fcfc1f0f1f6 0xede7bc7f3f07c3c7

def z191 : W := mkw 0x0000080402010404 0x4000002010080410 0x0108180c06030000 0x0004206030180c00

def z192 : W := mkw 0x37f90847b7bb84b4 0x40dfe4211edeee12 0x3ffb18cfffff0033 0xf4ffec633ffffc00

def z193 : W := mkw 0x0000081402050644 0x4000002050081419 0x0138183e063f0e1b 0xb404e060f818fc38

def z194 : W := mkw 0x0807d7ea4050d19b 0x0c201f5fa9014346 0xc007fffc0000f1cc 0x0b001ffff00003c7

def z195 : W := mkw 0x0001004200108090 0x0000040108004202 0x00000002003081d0 0x040000000800c207

def z196 : W := mkw 0x18a705c2c170d19b 0x04629c170b05c346 0x79ff07c3c7fff1f7 0xfde7fc1f0f1fffc7

def z197 : W := mkw 0x0806900000000000 0x00201a4000000000 0x8007f8000000000c 0x02001fe000000000

def z198 : W := mkw 0x3da705c3e570d19b 0x04f69c170f95c346 0x7fe707c3fff0f1f7 0xfdff9c1f0fffc3c7

def z199 : W := mkw 0x7ffed7b810cc1342 0x89fffb5ee043304d 0xfffffffc01cc01cf 0xeffffffff0073007

def z200 : W := mkw 0x12f8005491bf02e0 0x404be0015246fc0b 0x00f800fc01ff01c2 0x0c03e003f007fc07

def z201 : W := mkw 0x4000210018c83902 0x81000084006320e4 0x0000000039c07020 0x0000000000e701c0

def z202 : W := mkw 0x800128024a00ec1c 0x020004a0092803b0 0x000000000000fe00 0x00000000000003f8

def z203 : W := mkw 0xad06b0016c006808 0x02b41ac005b001a0 0xbf07f801f800702d 0xe2fc1fe007e001c0

def z204 : W := mkw 0xad06b0016c006808 0x02b41ac005b001a0 0xbe04e001f800fe3d 0x72f8138007e003f8

def z205 : W := mkw 0x4a57633258ccfb5a 0x81295d8cc96333ed 0xfed7e733f9ccffff 0xfffb5f9ccfe733ff

def z206 : W := mkw 0x40016b760a55bfd6 0xc10005add82956ff 0xc007fffc0000ffcc 0x0b001ffff00003ff

def z207 : W := mkw 0x4250633018cc3b42 0x8109418cc06330ed 0xc6d4e73039cc71e2 0x4f1b539cc0e731c7

def z208 : W := mkw 0x8807feaa4a00ec1c 0x0a201ffaa92803b0 0xc007fffc0000fe0c 0x0b001ffff00003f8

def z209 : W := mkw 0xad06b8016e006c0c 0x02b41ae005b801b0 0xbf04f801fe007e29 0x52fc13e007f801f8

def z210 : W := mkw 0x3ffed6a9b5aa0020 0x08fffb5aa6d6a800 0xfffce703ffff0033 0xf7fff39c0ffffc00

def z211 : W := mkw 0x00010856021586d4 0x400004215808561b 0x012b18fe06338fcc 0x8804ac63f818ce3f

def z212 : W := mkw 0x00000054001502c0 0x400000015000540b 0x013800fe063f01d3 0xbc04e003f818fc07

def z213 : W := mkw 0x0000200008002800 0x00000080002000a0 0x8604e00038007020 0x4218138000e001c0

def z214 : W := mkw 0x0000000000000000 0x0000000000000000 0x000400000000f034 0x60001000000003c0

def z215 : W := mkw 0x12f8000000000000 0x004be00000000000 0x00f8000000000002 0x0003e00000000000

def z216 : W := mkw 0x4250633018cc3b42 0x8109418cc06330ed 0xc6c4e70039ccfff0 0x571b139c00e733ff

def z217 : W := mkw 0x00010956c375d7df 0x440004255b0dd75f 0x013b18ffc7ffffff 0xbc04ec63ff1fffff

def z218 : W := mkw 0xa500b0012c002800 0x029402c004b000a0 0x8600e00038000000 0x0218038000e00000

def z219 : W := mkw 0x18a704c2c130c099 0x04629c130b04c302 0x38e300c3c1f00032 0xe4e38c030f07c000

def z220 : W := mkw 0x0000080002000404 0x0000002000080010 0x0100180006000e09 0x1004006000180038

def z221 : W := mkw 0x00010856021586d4 0x400004215808561b 0x0000000000008fc0 0x000000000000023f

def z222 : W := mkw 0x00010856021586d4 0x400004215808561b 0x000318fe063f8fdc 0x1c000c63f818fe3f

def z223 : W := mkw 0x2758d229348a0020 0x089d6348a4d22800 0x8718f83c3e0f0009 0x121c63e0f0f83c00

def z224 : W := mkw 0x800128036e00ec1c 0x020004a00db803b0 0x8604e003fe00fe3d 0x721813800ff803f8

def z225 : W := mkw 0x3ffe9001b5aa0020 0x00fffa4006d6a800 0xbffff803ffff003f 0xf6ffffe00ffffc00

def z226 : W := mkw 0x0001080202008414 0x0000042008080210 0x013b18fe06008e1f 0xb804ec63f8180238

def z227 : W := mkw 0x3fffdeaa02008414 0x08ffff7aa8080210 0xfffffffe06008e1f 0xfbfffffff8180238

def z228 : W := mkw 0x3ffe048000000000 0x00fff81200000000 0x7fff07c000000007 0xe9fffc1f00000000

def z229 : W := mkw 0x42506230188c2a40 0x81094188c06230a9 0x86d0e03039cc0e3b 0x761b4380c0e73038

def z230 : W := mkw 0x18a705c24050d19b 0x04629c1709014346 0x78e707c00000f1c6 0xe9e39c1f000003c7

def z231 : W := mkw 0x0001000200008010 0x0000040008000200 0x0003000200008014 0xa0000c0008000200

def z232 : W := mkw 0x18a6048000000000 0x0062981200000000 0x79ff1ffc0000000f 0xe9e7fc7ff0000000

def z233 : W := mkw 0x3ffed6a800000000 0x08fffb5aa0000000 0xfffffffe063f001f 0xfffffffff818fc00

def z234 : W := mkw 0x3ffed7e881701183 0x0cfffb5fa205c046 0xfffffffc01f001cf 0xeffffffff007c007

def z235 : W := mkw 0x4250211018cc3b42 0x81094084406330ed 0x06d0000039ccfff3 0x741b400000e733ff

def z236 : W := mkw 0x35a80001b5aa0020 0x00d6a00006d6a800 0x39280003ffff0030 0x94e4a0000ffffc00

def z237 : W := mkw 0x37f805c1b5fa11a3 0x04dfe01706d7e846 0x7ff807c3ffff01f3 0xfdffe01f0ffffc07

def z238 : W := mkw 0xe750fa313e8c2e44 0x839d43e8c4fa30b9 0x8710f8303e0c0e09 0x121c43e0c0f83038

def z239 : W := mkw 0x4250633008443b42 0x8109418cc02110ed 0xc6d4e7300000ffcf 0x6b1b539cc00003ff

def z240 : W := mkw 0xffffffbb7eccff5e 0x8bfffffeedfb33fd 0xffffffffffccffff 0xffffffffffff33ff

def z241 : W := mkw 0xbffffeab6e00ec1c 0x0afffffaadb803b0 0xfffffffffe00fe3f 0xfbfffffffff803f8

def z242 : W := mkw 0x080705c24050d19b 0x04201c1709014346 0x40c707c001c0f1f6 0x6d031c1f000703c7

def z243 : W := mkw 0x18a6048000000000 0x0062981200000000 0x382300c000000000 0x80e08c0300000000

def z244 : W := mkw 0x40002111bdee3b62 0x8100008446f7b8ed 0x00000003fffffff0 0x140000000fffffff

def z245 : W := mkw 0xad07b8036e00ec1c 0x02b41ee00db803b0 0xbf3ff8fffe00fe3f 0xfafcffe3fff803f8

def z246 : W := mkw 0x12f847e881701183 0x0c4be11fa205c046 0x40f807fc01f001c2 0x0d03e01ff007c007

def z247 : W := mkw 0x42506331bdee3b62 0x8109418cc6f7b8ed 0xc6d4e733ffffffff 0x7f1b539ccfffffff

def z248 : W := mkw 0xbda7bd83ef60fd1f 0x06f69ef60fbd83f4 0xffc7ff03ffc0fe3d 0xf3ff1ffc0fff03f8

def z249 : W := mkw 0x00010856021586d4 0x400004215808561b 0x000318fc00008fcc 0x08000c63f000023f

def z250 : W := mkw 0x37f80001b5aa0020 0x00dfe00006d6a800 0x3ec00001f9c00020 0x40fb000007e70000

def z251 : W := mkw 0xad07b8036e00ec1c 0x02b41ee00db803b0 0xb907f803c600fe0c 0x82e41fe00f1803f8

def z252 : W := mkw 0x10a0010081601102 0x0042800402058044 0x78e40703c1f0f1f6 0xede3901c0f07c3c7

def z253 : W := mkw 0x12f80001b5aa0020 0x004be00006d6a800 0x00f80003ffff0032 0x1403e0000ffffc00

def z254 : W := mkw 0x0000000124000000 0x0000000004900000 0x00000003fe000030 0x100000000ff80000

def z255 : W := mkw 0x2500000124000000 0x0094000004900000 0x3f380003fe3f0033 0xf4fce0000ff8fc00

def z256 : W := mkw 0x0000210008403902 0x00000084002100e4 0xc6c4e70039c0ffff 0x7f1b139c00e703ff

def z257 : W := mkw 0xad07b8024a00ec1c 0x02b41ee0092803b0 0xbf07f8000000fe0d 0xe2fc1fe0000003f8

def z258 : W := mkw 0x4250433010cc1342 0x8109410cc043304d 0x46d0073039cc01f3 0x7d1b401cc0e73007

def z259 : W := mkw 0x08070142c170d19b 0x04201c050b05c346 0x38070003c1f0f1f4 0xe4e01c000f07c3c7

def z260 : W := mkw 0x5af76ff6dbfdffdf 0xc56bddbfdb6ff7ff 0xffffffffffffffff 0xffffffffffffffff

def z261 : W := mkw 0x4250622018882800 0x81094188806220a0 0x8600e00038000000 0x0218038000e00000

def z262 : W := mkw 0x42516b321accbf56 0x810945acc86b32fd 0xc7d7ff323fccffff 0xff1f5ffcc8ff33ff

def z263 : W := mkw 0xa500b8012e002c04 0x029402e004b800b0 0x8704f8003e00fe3d 0x721c13e000f803f8

def z264 : W := mkw 0x00010856021586d4 0x400004215808561b 0x01031802063f8fdd 0xb4040c600818fe3f

def z265 : W := mkw 0x0000000000000000 0x0000000000000000 0x01180000060f0001 0x1004600000183c00

def z266 : W := mkw 0x18a6d6a800000000 0x08629b5aa0000000 0xf8e7fffc0000000e 0xebe39ffff0000000

def z267 : W := mkw 0x3ffe900000000000 0x00fffa4000000000 0xbffff8000000000f 0xe2ffffe000000000

def z268 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000002063f0010 0x140000000818fc00

def z269 : W := mkw 0x0000001000040240 0x0000000040001009 0x0000003000008fcc 0x08000000c000023f

def z270 : W := mkw 0xbfffb803ffaaec3c 0x02fffee00ffeabb0 0xbfc7f803ffc0fe3d 0xf2ff1fe00fff03f8

def z271 : W := mkw 0x3ffed6a800000000 0x08fffb5aa0000000 0xffefffcc00000000 0xc3ffbfff30000000

def z272 : W := mkw 0x37f90857b7bf86f4 0x40dfe4215edefe1b 0x3ff80003ffff8ff3 0xf4ffe0000ffffe3f

def z273 : W := mkw 0x8807b8024a00ec1c 0x02201ee0092803b0 0xb807f803c000fe3c 0xe2e01fe00f0003f8

def z274 : W := mkw 0x0250000010880000 0x0009400000422000 0x00d0000001cc0002 0x0403400000073000

def z275 : W := mkw 0x0000010000401102 0x0000000400010044 0x0000000001c0f1f0 0x04000000000703c7

def z276 : W := mkw 0xc00129137eccff5e 0x830004a44dfb33fd 0x00000003ffccfff0 0x140000000fff33ff

def z277 : W := mkw 0x00000001348a0020 0x0000000004d22800 0x000000003e0f0000 0x1000000000f83c00

def z278 : W := mkw 0x0000081402050644 0x4000002050081419 0x0118183c060f8fdf 0x3c046060f0183e3f

def z279 : W := mkw 0x0000000000000000 0x0000000000000000 0x0118183c00000009 0x00046060f0000000

def z280 : W := mkw 0x4250433010cc1342 0x8109410cc043304d 0x40d4073001ccf1f6 0x6d03501cc00733c7

def z281 : W := mkw 0x0250200018882800 0x00094080006220a0 0x86d4e00039ccfe3f 0x761b538000e733f8

def z282 : W := mkw 0x3ffedebc02050644 0x48fffb7af0081419 0xfffffffc060f0e0f 0xfbfffffff0183c38

def z283 : W := mkw 0x0001084602118494 0x4000042118084612 0x000318cc00000000 0x00000c6330000000

def z284 : W := mkw 0x4000633008443b42 0x8100018cc02110ed 0xc604e7303800fffd 0x7b18139cc0e003ff

def z285 : W := mkw 0xef57fb237ec8fd1e 0x83bd5fec8dfb23f4 0xffc7ff03ffc0fe3d 0xf3ff1ffc0fff03f8

def z286 : W := mkw 0xbffeb001fdaa6828 0x02fffac007f6a9a0 0xbffce003ffff7033 0xf6fff3800ffffdc0

def z287 : W := mkw 0x40012152d9fcfbdb 0x850004854b67f3ef 0x00000003f9fcfff0 0x140000000fe7f3ff

def z288 : W := mkw 0x0000081402050644 0x4000002050081419 0x00000000060f0e00 0x1000000000183c38

def z289 : W := mkw 0x400129561addbfd6 0xc10004a5586b76ff 0x000000023ffffff0 0x1400000008ffffff

def z290 : W := mkw 0x080700424010c098 0x00201c0109004302 0x382700c3c030f1f6 0xece09c030f00c3c7

def z291 : W := mkw 0x00010856021586d4 0x400004215808561b 0x01380002063f8fd3 0xb404e0000818fe3f

def z292 : W := mkw 0x98a72dc3ef70fd9f 0x06629cb70fbdc3f6 0x78e707c3fff0fff6 0xfde39c1f0fffc3ff

def z293 : W := mkw 0x37f80001b5aa0020 0x00dfe00006d6a800 0x3ffb18ffffff003f 0xfcffec63fffffc00

def z294 : W := mkw 0x02514a76021586d4 0x40094529d808561b 0xc7fffffe063f8fdf 0xff1ffffff818fe3f

def z295 : W := mkw 0x00010142c170d19b 0x040004050b05c346 0x40c40703c1f0f1f6 0x6d03101c0f07c3c7

def z296 : W := mkw 0x18a705c2c170d19b 0x04629c170b05c346 0x78e307c3c1f001c2 0x8de38c1f0f07c007

def z297 : W := mkw 0x0000201008042a40 0x00000080402010a9 0x8614e030380cffff 0x7e185380c0e033ff

def z298 : W := mkw 0x10a105c281709193 0x044284170a05c246 0x40e307c201f081d6 0xad038c1f0807c207

def z299 : W := mkw 0xbda7bcc3ef30ec9d 0x06f69ef30fbcc3b2 0xbf27f8c3fe30fe3d 0xf2fc9fe30ff8c3f8

def z300 : W := mkw 0x3ffed6a810880000 0x08fffb5aa0422000 0xfffffffc39cc003f 0xfffffffff0e73000

def z301 : W := mkw 0x7ffffffe1addbfd6 0xc9fffffff86b76ff 0xfffffffe3fffffff 0xfffffffff8ffffff

def z302 : W := mkw 0x0250422000000000 0x0009410880000000 0xc7fffffc0000000f 0xeb1ffffff0000000

def z303 : W := mkw 0x880798024200c41c 0x02201e6009080310 0x0003180000000000 0x00000c6000000000

def z304 : W := mkw 0xad07bdc36e50fd9f 0x06b41ef70db943f6 0xff07ffc3fe00fffd 0xfbfc1fff0ff803ff

def z305 : W := mkw 0x0258422800000000 0x08096108a0000000 0x0018003c00000000 0x00006000f0000000

def z306 : W := mkw 0x18a704824000c018 0x00629c1209000300 0x78e707c3c000f036 0xe9e39c1f0f0003c0

def z307 : W := mkw 0x08070dd64255d7df 0x44201c375909575f 0x413f1ffe063fffdf 0xbd04fc7ff818ffff

def z308 : W := mkw 0x5af667b0d9ec7b4b 0x856bd99ec367b1ed 0xfed4e731f9ccffff 0x7ffb539cc7e733ff

def z309 : W := mkw 0x3ffed6b800040240 0x08fffb5ae0001009 0xfffffffc000c8fdf 0xfffffffff000323f

def z310 : W := mkw 0xbda7b803ef20ec1c 0x02f69ee00fbc83b0 0xbfe7f803fff0fe3f 0xf6ff9fe00fffc3f8

def z311 : W := mkw 0x18a70cd6021586d4 0x40629c335808561b 0x79ff1ffe063f8fdf 0xfde7fc7ff818fe3f

def z312 : W := mkw 0x00010142c170d19b 0x040004050b05c346 0x002300c3c1f0f1f6 0xac008c030f07c3c7

def z313 : W := mkw 0x18a705d2c174d3db 0x04629c174b05d34f 0x78f707f3c1fcffff 0xfde3dc1fcf07f3ff

def z314 : W := mkw 0x37f80001b5aa0020 0x00dfe00006d6a800 0x3fe80003fff30020 0xc0ffa0000fffcc00

def z315 : W := mkw 0x2758000000000000 0x009d600000000000 0x0718000000000001 0x001c600000000000

def z316 : W := mkw 0xa501b8036e00ec1c 0x029406e00db803b0 0x8700f803fe00fe39 0x121c03e00ff803f8

def z317 : W := mkw 0x37f80001b5aa0020 0x00dfe00006d6a800 0x3ee00003f9f00032 0xe4fb80000fe7c000

def z318 : W := mkw 0x3da795c2c170d19b 0x04f69e570b05c346 0xffe7ffc3c1f0f1ff 0xefff9fff0f07c3c7

def z319 : W := mkw 0xad07b803ffaaec3c 0x02b41ee00ffeabb0 0xbf07f803fffffe3d 0xf6fc1fe00ffffff8

def z320 : W := mkw 0xbffffeab6e00ec1c 0x0afffffaadb803b0 0xffc7ff03fe00fe3d 0xf3ff1ffc0ff803f8

def z321 : W := mkw 0x4000211018cc3b42 0x81000084406330ed 0x0010003039ccffff 0x3c004000c0e733ff

def z322 : W := mkw 0x40016b760a55bfd6 0xc10005add82956ff 0xc13ffffe063fffdf 0xbf04fffff818ffff

def z323 : W := mkw 0x0250422000000000 0x0009410880000000 0x40d0073000000002 0x0903401cc0000000

def z324 : W := mkw 0x0806d6a800000000 0x08201b5aa0000000 0xc13ffffc0000000f 0xab04fffff0000000

def z325 : W := mkw 0xad07b8136e04ee5c 0x02b41ee04db813b9 0xbf17f833fe0cffff 0xfefc5fe0cff833ff

def z326 : W := mkw 0x0001004200108090 0x0000040108004202 0x013b18fe003081df 0xac04ec63f800c207

def z327 : W := mkw 0x2758d22800000000 0x089d6348a0000000 0x8600e00000000000 0x0218038000000000

def z328 : W := mkw 0xb7f8b801bfaa2c24 0x02dfe2e006fea8b0 0xbff8f803ffff0e3b 0xf6ffe3e00ffffc38

def z329 : W := mkw 0x0000200008002800 0x00000080002000a0 0x000000003800fe30 0x1000000000e003f8

def z330 : W := mkw 0x2d06d6a800000000 0x08b41b5aa0000000 0xff07fffc0000000d 0xebfc1ffff0000000

def z331 : W := mkw 0xbda79cc3e730c49d 0x06f69e730f9cc312 0x392318c3c6300000 0x80e48c630f18c000

def z332 : W := mkw 0x0000422000000000 0x0000010880000000 0xc004e7300000000c 0x0b00139cc0000000

def z333 : W := mkw 0x00010956c375d7df 0x440004255b0dd75f 0x00000003c7fffff0 0x140000000f1fffff

def z334 : W := mkw 0x0250422000000000 0x0009410880000000 0x8610e03000000009 0x02184380c0000000

def z335 : W := mkw 0xad0798036600c41c 0x02b41e600d980310 0xbf07f803c600000d 0xe2fc1fe00f180000

def z336 : W := mkw 0xad07b0036c00e818 0x02b41ec00db003a0 0xbe07e003f800f034 0xe2f81f800fe003c0

def z337 : W := mkw 0x42516b761addbfd6 0xc10945add86b76ff 0xc6d7fffc39ccffff 0x7f1b5ffff0e733ff

def z338 : W := mkw 0x080700024000c018 0x00201c0009000300 0x38030003c0000000 0x80e00c000f000000

def z339 : W := mkw 0x7ffef7b818cc3b42 0x89fffbdee06330ed 0xfed4e73039ccffff 0x7ffb539cc0e733ff

def z340 : W := mkw 0x0250422010880000 0x0009410880422000 0xc6d4e73039cc003f 0x7f1b539cc0e73000

def z341 : W := mkw 0x00010856021586d4 0x400004215808561b 0x013b18fc00008fcf 0xa804ec63f000023f

def z342 : W := mkw 0x0001084602118494 0x4000042118084612 0x013b18ce063f0013 0xb404ec633818fc00

def z343 : W := mkw 0x00010856021586d4 0x400004215808561b 0x002318fe00308fde 0xac008c63f800c23f

def z344 : W := mkw 0x80012803ffaaec3c 0x020004a00ffeabb0 0x00000003fffffe30 0x140000000ffffff8

def z345 : W := mkw 0x0000000000000000 0x0000000000000000 0x8604e0000000000d 0x6218138000000000

def z346 : W := mkw 0x2f56d22000000000 0x00bd5b4880000000 0xffd7ff300000000f 0xebff5ffcc0000000

def z347 : W := mkw 0x0000000000000000 0x0000000000000000 0x003800fc00000002 0x0800e003f0000000

def z348 : W := mkw 0x52f847b810cc1342 0x894be11ee043304d 0x40f807fc01cc01c2 0x0d03e01ff0073007

def z349 : W := mkw 0x3ffed6a800000000 0x08fffb5aa0000000 0xffdcff3c00000009 0x43ff73fcf0000000

def z350 : W := mkw 0x18a6048000000000 0x0062981200000000 0x78c4070000000000 0x41e3101c00000000

def z351 : W := mkw 0x8807b8564a15eedc 0x42201ee1592857bb 0x8007f8fc0000ffcc 0x0a001fe3f00003ff

def z352 : W := mkw 0x37f90043b5ba80b0 0x00dfe4010ed6ea02 0x3ffb00c3ffff81f7 0xfcffec030ffffe07

def z353 : W := mkw 0x3ffe0581f5ea512b 0x04fff81607d7a944 0x7ffc0703ffff7033 0xf5fff01c0ffffdc0

def z354 : W := mkw 0xad07b8036e00ec1c 0x02b41ee00db803b0 0xbe07f801f800fe2c 0x42f81fe007e003f8

def z355 : W := mkw 0x35a80001a5220020 0x00d6a00006948800 0x39380003c63f0013 0xb4e4e0000f18fc00

def z356 : W := mkw 0x00010856021586d4 0x400004215808561b 0x001318fc000c8fdf 0x3c004c63f000323f

def z357 : W := mkw 0x3ffed6a800000000 0x08fffb5aa0000000 0xfee7e7c000000006 0xebfb9f9f00000000

def z358 : W := mkw 0x2d06900000000000 0x00b41a4000000000 0xbe04e00000000000 0x42f8138000000000

def z359 : W := mkw 0x18a70cd6c335c6dd 0x44629c335b0cd71b 0x393b18ffc63f8fdf 0xbce4ec63ff18fe3f

def z360 : W := mkw 0xa50128036e00ec1c 0x029404a00db803b0 0x3f000003fe00fe31 0xf0fc00000ff803f8

def z361 : W := mkw 0x35a90847a73384b4 0x40d6a4211e9cce12 0x392b18cfc6330000 0x80e4ac633f18cc00

def z362 : W := mkw 0x4250632018c83902 0x8109418c806320e4 0xc6d4e73039c0702f 0x6b1b539cc0e701c0

def z363 : W := mkw 0x0000001000040240 0x0000000040001009 0x00100030000c0e09 0x10004000c0003038

def z364 : W := mkw 0x0000001000040240 0x0000000040001009 0x00100030000c01c2 0x0c004000c0003007

def z365 : W := mkw 0x000101424050d19b 0x0400040509014346 0x000000000000f1c0 0x00000000000003c7

def z366 : W := mkw 0x2508000124020020 0x0094200004900800 0x0108000006030000 0x0004200000180c00

def z367 : W := mkw 0xad06b0016c006808 0x02b41ac005b001a0 0xbf04e003fe007031 0xf2fc13800ff801c0

def z368 : W := mkw 0x18a705d6c175d3db 0x44629c175b05d74f 0x78ff07ffc1fff1f6 0xede3fc1fff07ffc7

def z369 : W := mkw 0x0001084602118494 0x4000042118084612 0x013b18fe0633000f 0xa804ec63f818cc00

def z370 : W := mkw 0x10a10142c170d19b 0x044284050b05c346 0x38e00003c1f0f1f2 0xe4e380000f07c3c7

def z371 : W := mkw 0x2500000124000000 0x0094000004900000 0x39000003c6000000 0x80e400000f180000

def z372 : W := mkw 0x42506230188c2a40 0x81094188c06230a9 0x8610e030380c8fdf 0x3e184380c0e0323f

def z373 : W := mkw 0x3ffed6a9b5aa0020 0x08fffb5aa6d6a800 0xfffffffdf9c0002f 0xebfffffff7e70000

def z374 : W := mkw 0xad07b8576e15eedc 0x42b41ee15db857bb 0xbf07f803fe3ffffd 0xf6fc1fe00ff8ffff

def z375 : W := mkw 0x2758d22800000000 0x089d6348a0000000 0xc7dcff3c0000000f 0x6b1f73fcf0000000

def z376 : W := mkw 0x00000854021506c4 0x400000215008541b 0x013818fc063f0fcb 0x1c04e063f018fc3f

def z377 : W := mkw 0x1aff47eac170d19b 0x0c6bfd1fab05c346 0x78ff07ffc1f0f1f6 0xede3fc1fff07c3c7

def z378 : W := mkw 0xa501b8032e00ac14 0x029406e00cb802b0 0x8703f8023e008e1d 0xb21c0fe008f80238

def z379 : W := mkw 0x12f8000091aa0020 0x004be0000246a800 0x00c0000001c00000 0x0003000000070000

def z380 : W := mkw 0x3fffd7eac170d19b 0x0cffff5fab05c346 0xfee7e7c3c1f0f1f6 0xeffb9f9f0f07c3c7

def z381 : W := mkw 0x0250000010880000 0x0009400000422000 0x07f800023fff0033 0xf41fe00008fffc00

def z382 : W := mkw 0xbda7b5c3ed70f99b 0x06f69ed70fb5c3e6 0xfee7e7c3f9f0f1f6 0xeffb9f9f0fe7c3c7

def z383 : W := mkw 0x18a7d7eac170d19b 0x0c629f5fab05c346 0xf8e7ffffc1f0f1fe 0xefe39fffff07c3c7

def z384 : W := mkw 0x00000054001502c0 0x400000015000540b 0x00000000003f01c0 0x040000000000fc07

def z385 : W := mkw 0x4250637418dd3bc2 0xc109418dd06374ef 0xc6fce7fc39ffffff 0x7f1bf39ff0e7ffff

def z386 : W := mkw 0x00010056001582d0 0x400004015800560b 0x003b00fe003f81d6 0xac00ec03f800fe07

def z387 : W := mkw 0x2d06b00008002800 0x00b41ac0002000a0 0xbf07f8003800fe3d 0xf2fc1fe000e003f8

def z388 : W := mkw 0x35a80001a5220020 0x00d6a00006948800 0x3f280003fe330031 0xf0fca0000ff8cc00

def z389 : W := mkw 0x3fff05c3f5fad1bb 0x04fffc170fd7eb46 0x7ee707c3f9f0f1f6 0xedfb9c1f0fe7c3c7

def z390 : W := mkw 0x3dae9489a5220020 0x08f6ba5226948800 0x392b18cfc6330000 0x80e4ac633f18cc00

def z391 : W := mkw 0x080705c24050d19b 0x04201c1709014346 0x780707c3c000f1f4 0xe9e01c1f0f0003c7

def z392 : W := mkw 0x1af747e2c170d19b 0x046bdd1f8b05c346 0xfef7e7f3c1f0f1ff 0xeffbdf9fcf07c3c7

def z393 : W := mkw 0x12f846a800000000 0x084be11aa0000000 0xc6fce7fc0000000f 0x6b1bf39ff0000000

def z394 : W := mkw 0x35a90857a73786f4 0x40d6a4215e9cde1b 0x393b18ffc63f8fdf 0xbce4ec63ff18fe3f

def z395 : W := mkw 0xbda7bdd7ef75ffdf 0x46f69ef75fbdd7ff 0xffffffffffffffff 0xffffffffffffffff

def z396 : W := mkw 0x2500000124000000 0x0094000004900000 0x3e000001f8000020 0x40f8000007e00000

def z397 : W := mkw 0x0000000000000000 0x0000000000000000 0x00100000000c0013 0x3400400000003000

def z398 : W := mkw 0x4000632008403902 0x8100018c802100e4 0xc004e70000007000 0x0300139c000001c0

def z399 : W := mkw 0x0001080202008414 0x0000042008080210 0x0003180000008e0c 0x00000c6000000238

def z400 : W := mkw 0x35a80001a5220020 0x00d6a00006948800 0x39e80003c7f30032 0xe4e7a0000f1fcc00

def z401 : W := mkw 0x00000001a5220020 0x0000000006948800 0x00000003c6330000 0x000000000f18cc00

def z402 : W := mkw 0x02510856129d86d4 0x40094421584a761b 0x07fb18fe3fff8fff 0xfc1fec63f8fffe3f

def z403 : W := mkw 0x58a725d2d9fcfbdb 0x85629c974b67f3ef 0x78e707c3f9fcfff6 0xfde39c1f0fe7f3ff

def z404 : W := mkw 0x0000d22800000000 0x08000348a0000000 0x8000f83c00000008 0x020003e0f0000000

def z405 : W := mkw 0x2500000124000000 0x0094000004900000 0x070000003e000001 0x101c000000f80000

def z406 : W := mkw 0x52f047f091fc13c3 0x854bc11fc247f04f 0x40f007f001fc01c2 0x0d03c01fc007f007

def z407 : W := mkw 0xbfffb857ffbfeefc 0x42fffee15ffeffbb 0xbffff8ffffffffff 0xfeffffe3ffffffff

def z408 : W := mkw 0x0000001000040240 0x0000000040001009 0x00000000000c8fd0 0x140000000000323f

def z409 : W := mkw 0x0000081402050644 0x4000002050081419 0x013b18fc060f0e0f 0xb804ec63f0183c38

def z410 : W := mkw 0x0001004200108090 0x0000040108004202 0x000300c0000081c4 0x08000c0300000207

def z411 : W := mkw 0x0250000010880000 0x0009400000422000 0x06100000380c0001 0x1018400000e03000

def z412 : W := mkw 0x0001084602118494 0x4000042118084612 0x012b18ce063381d6 0xac04ac633818ce07

def z413 : W := mkw 0x0001084602118494 0x4000042118084612 0x012b18ce06338e1d 0xb004ac633818ce38

def z414 : W := mkw 0x8806b00048006808 0x02201ac0012001a0 0x8004e00000007000 0x02001380000001c0

def z415 : W := mkw 0x0000000000000000 0x0000000000000000 0x0128000206330000 0x8004a0000818cc00

def z416 : W := mkw 0x0000000000000000 0x0000000000000000 0x001000300000000f 0x28004000c0000000

def z417 : W := mkw 0x2d07980202008414 0x00b41e6008080210 0xbf07f80206008e1d 0xf2fc1fe008180238

def z418 : W := mkw 0x7ffff7fad9fcfbdb 0x8dffffdfeb67f3ef 0xfffffffff9fcffff 0xffffffffffe7f3ff

def z419 : W := mkw 0x7ffef6b8188c2a40 0x89fffbdae06230a9 0xfffffffc380c0e0f 0xfbfffffff0e03038

def z420 : W := mkw 0xbfff9803f7aac43c 0x02fffe600fdeab10 0x3ffb1803ffff0033 0xf4ffec600ffffc00

def z421 : W := mkw 0xad0798476611c49c 0x42b41e611d984712 0x392b18cfc6330000 0x80e4ac633f18cc00

def z422 : W := mkw 0x4000633008443b42 0x8100018cc02110ed 0xc0c4e73001c0fffe 0x6f03139cc00703ff

def z423 : W := mkw 0x3daf94cac130c099 0x0cf6be532b04c302 0x392b18cfc0300000 0x80e4ac633f00c000

def z424 : W := mkw 0xaf5ffa2b6e00ec1c 0x0abd7fe8adb803b0 0xbf1ff83ffe00fe3d 0xf2fc7fe0fff803f8

def z425 : W := mkw 0x37f90856021586d4 0x40dfe4215808561b 0x3ffb18fe063f8fdf 0xfcffec63f818fe3f

def z426 : W := mkw 0x3dae948800000000 0x08f6ba5220000000 0xbf2ff8cc0000000d 0xe2fcbfe330000000

def z427 : W := mkw 0x2d0790024000c018 0x00b41e4009000300 0xbf07f803c000f03d 0xe2fc1fe00f0003c0

def z428 : W := mkw 0x37f846a9b5aa0020 0x08dfe11aa6d6a800 0x7ff807ffffff0033 0xfdffe01ffffffc00

def z429 : W := mkw 0xef57fb777eddffde 0xc3bd5fedddfb77ff 0xffffffffffffffff 0xffffffffffffffff

def z430 : W := mkw 0x35a00001a5200000 0x00d6800006948000 0x3fe00003fff00033 0xf4ff80000fffc000

def z431 : W := mkw 0x675063313ccc3b42 0x819d418cc4f330ed 0xffd4e733ffccffff 0xffff539ccfff33ff

def z432 : W := mkw 0x18a605c081701183 0x046298170205c046 0x78e707c001f001c6 0xede39c1f0007c007

def z433 : W := mkw 0x80012943ef70fd9f 0x060004a50fbdc3f6 0x00000003fff0fff0 0x140000000fffc3ff

def z434 : W := mkw 0x10a10dd6837597d7 0x444284375a0dd65f 0x41fb1ffe07ff8fdf 0xbd07ec7ff81ffe3f

def z435 : W := mkw 0x4250633018cc3b42 0x8109418cc06330ed 0xc6d4e73039cc7e29 0x531b539cc0e731f8

def z436 : W := mkw 0x10a0000081200000 0x0042800002048000 0x38c00001c1c00020 0x40e3000007070000

def z437 : W := mkw 0x10a00001b5aa0020 0x0042800006d6a800 0x38e00003ffff0032 0xf4e380000ffffc00

def z438 : W := mkw 0x37f80001b5aa0020 0x00dfe00006d6a800 0x3f380003fe3f0001 0x90fce0000ff8fc00

def z439 : W := mkw 0x0001084202108494 0x0000042108084212 0x012318c206308fdf 0xbc048c630818c23f

def z440 : W := mkw 0x0806d6a800000000 0x08201b5aa0000000 0xc004e70000000000 0x0300139c00000000

def z441 : W := mkw 0x0000000000000000 0x0000000000000000 0x38000003c0000030 0xe0e000000f000000

def z442 : W := mkw 0x37f80001348a0020 0x00dfe00004d22800 0x3ff800003e0f0003 0xf0ffe00000f83c00

def z443 : W := mkw 0x7fff67f3fdfefbfb 0x85fffd9fcff7fbef 0xffffe7f3ffffffff 0xffffff9fcfffffff

def z444 : W := mkw 0xe750fb313ecc3f46 0x839d43ecc4fb30fd 0xc7d4ff303fccffff 0x7f1f53fcc0ff33ff

def z445 : W := mkw 0x00010857b7bf86f4 0x400004215edefe1b 0x013b18ffffff8fff 0xbc04ec63fffffe3f

def z446 : W := mkw 0x2d06900000000000 0x00b41a4000000000 0x3903180000000000 0x80e40c6000000000

def z447 : W := mkw 0x27580001348a0020 0x009d600004d22800 0x0600000038000000 0x0018000000e00000

def z448 : W := mkw 0x000100024000c018 0x0000040009000300 0x00000003c000f030 0x000000000f0003c0

def z449 : W := mkw 0xbfffb8036e00ec1c 0x02fffee00db803b0 0xbffff803fe00fe3f 0xf2ffffe00ff803f8

def z450 : W := mkw 0x0000000010880000 0x0000000000422000 0x0000000039cc0030 0x1400000000e73000

def z451 : W := mkw 0x080701024040d11a 0x00201c0409010344 0x78c70703c1c0f1f6 0xede31c1c0f0703c7

def z452 : W := mkw 0x3ffed7a8c160510b 0x0cfffb5ea3058144 0xfffffffdc1c0702f 0xebfffffff70701c0

def z453 : W := mkw 0x4250633018cc3b42 0x8109418cc06330ed 0xc7fffffc39ccffff 0xff1ffffff0e733ff

def z454 : W := mkw 0xad06b8012e002c04 0x02b41ae004b800b0 0xbf07f8003e000e0d 0xf2fc1fe000f80038

def z455 : W := mkw 0xaf57fa236e00ec1c 0x02bd5fe88db803b0 0xffd7ff33fe00fe3f 0xfbff5ffccff803f8

def z456 : W := mkw 0x37f80001b5aa0020 0x00dfe00006d6a800 0x39f80003c7ff0002 0x84e7e0000f1ffc00

def z457 : W := mkw 0x2501080326008414 0x009404200c980210 0x3f031803fe008e3d 0xf0fc0c600ff80238

def z458 : W := mkw 0x0000000000000000 0x0000000000000000 0x012b18cc00000000 0x8004ac6330000000

def z459 : W := mkw 0xa501b8572e15aed4 0x429406e15cb856bb 0x873bf8fe3e3f8fdf 0xbe1cefe3f8f8fe3f

def z460 : W := mkw 0xaf5fb8037e8aec3c 0x02bd7ee00dfa2bb0 0xbf1ff803fe0ffe3d 0xf2fc7fe00ff83ff8

def z461 : W := mkw 0x42516a761a9daed4 0xc10945a9d86a76bb 0x873bf8fe3e3f8fdf 0xbe1cefe3f8f8fe3f

def z462 : W := mkw 0xa758fa292e002c04 0x0a9d63e8a4b800b0 0x8718f83c3e000e09 0x121c63e0f0f80038

def z463 : W := mkw 0xbffffeff6e15eedc 0x4afffffbfdb857bb 0xfffffffffe3fffff 0xfffffffffff8ffff

def z464 : W := mkw 0x00010143f5fad1bb 0x040004050fd7eb46 0x00000003fffff1f0 0x140000000fffffc7

def z465 : W := mkw 0x37f8d229b5aa0020 0x08dfe348a6d6a800 0xbff8f83fffff003b 0xf6ffe3e0fffffc00

def z466 : W := mkw 0x0001080202008414 0x0000042008080210 0x013b1802063f8e1f 0xb404ec600818fe38

def z467 : W := mkw 0x52f8633099ee3b62 0x814be18cc267b8ed 0xc6fce73039ffffff 0x7f1bf39cc0e7ffff

def z468 : W := mkw 0x4000011010cc1342 0x810000044043304d 0x0000000001cc01c0 0x0400000000073007

def z469 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000000081d6 0x2c00000000000207

def z470 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000008e1d 0x3000000000000238

def z471 : W := mkw 0x0000200008002800 0x00000080002000a0 0x8600e00038000e09 0x1218038000e00038

def z472 : W := mkw 0xef57fa337e8cee5c 0x83bd5fe8cdfa33b9 0xbf17f833fe0cfe3d 0xf2fc5fe0cff833f8

def z473 : W := mkw 0x0250432000401102 0x0009410c80010044 0xc6d4e73001c0f1ff 0x6f1b539cc00703c7

def z474 : W := mkw 0xad06900164004008 0x02b41a4005900100 0x38000001c0000000 0x00e0000007000000

def z475 : W := mkw 0x37f80001b5aa0020 0x00dfe00006d6a800 0x3ef80001f9ff0022 0x44fbe00007e7fc00

def z476 : W := mkw 0x0001004200108090 0x0000040108004202 0x013b00c2063f81d7 0xbc04ec030818fe07

def z477 : W := mkw 0x98a7bdc2cb70fd9f 0x06629ef70b2dc3f6 0xf8e7ffc3c1f0fffe 0xefe39fff0f07c3ff

def z478 : W := mkw 0x3da6948000000000 0x00f69a5200000000 0xffe7ffc00000000f 0xebff9fff00000000

def z479 : W := mkw 0xbffffeaa4a00ec1c 0x0afffffaa92803b0 0xfffffffc0000fe0f 0xebfffffff00003f8

def z480 : W := mkw 0x18a705c2c170d19b 0x04629c170b05c346 0x40e707c001f0f1c6 0x0d039c1f0007c3c7

def z481 : W := mkw 0x3ffed6a9348a0020 0x08fffb5aa4d22800 0xfffffffc3e0f000f 0xfbfffffff0f83c00

def z482 : W := mkw 0x37f80001b5aa0020 0x00dfe00006d6a800 0x07f800003fff0003 0x141fe00000fffc00

def z483 : W := mkw 0x27580001348a0020 0x009d600004d22800 0x3f180003fe0f0031 0xf0fc60000ff83c00

def z484 : W := mkw 0x77f86321bdea3922 0x81dfe18c86f7a8e4 0xfec4e701f9c07020 0x43fb139c07e701c0

def z485 : W := mkw 0x0806000000000000 0x0020180000000000 0x3807000000000004 0xe0e01c0000000000

def z486 : W := mkw 0xbda6b581ed60790b 0x06f69ad607b581e4 0xfec4e701f9c07020 0x43fb139c07e701c0

def z487 : W := mkw 0x3ffed6a9a5220020 0x08fffb5aa6948800 0xffffffffc633000f 0xebffffffff18cc00

def z488 : W := mkw 0xc807fb324a44ff5e 0x83201fecc92913fd 0xc007ff300000ffcc 0x0b001ffcc00003ff

def z489 : W := mkw 0x2500900000000000 0x0094024000000000 0x8700f80000000009 0x021c03e000000000

def z490 : W := mkw 0x0000000000000000 0x0000000000000000 0x000318fc0000000c 0x08000c63f0000000

def z491 : W := mkw 0x18a705c2c170d19b 0x04629c170b05c346 0x79ff1fffc1f0f1ff 0xede7fc7fff07c3c7

def z492 : W := mkw 0x0000014081701183 0x040000050205c046 0x0000000001f001c0 0x040000000007c007

def z493 : W := mkw 0x7ffef7b9bdee3b62 0x89fffbdee6f7b8ed 0xffffffffffffffff 0xffffffffffffffff

def z494 : W := mkw 0x080605804040510b 0x0420181601010144 0x4004070000007000 0x0100101c000001c0

def z495 : W := mkw 0x35a8000000000000 0x00d6a00000000000 0x3928000000000000 0x80e4a00000000000

def z496 : W := mkw 0x0000001000040240 0x0000000040001009 0x01380032063f8fdf 0xbc04e000c818fe3f

def z497 : W := mkw 0x3ffed6a800000000 0x08fffb5aa0000000 0x79fb1ffc00000002 0x89e7ec7ff0000000

def z498 : W := mkw 0x0000010000401102 0x0000000400010044 0x400407000000f1c4 0x0900101c000003c7

def z499 : W := mkw 0x0250622008002800 0x00094188802000a0 0xc6d4e7303800fe3f 0x7b1b539cc0e003f8

def z500 : W := mkw 0x18a70cc6c331c49d 0x44629c331b0cc712 0x392b18cfc6330000 0x80e4ac633f18cc00

def z501 : W := mkw 0x00010856021586d4 0x400004215808561b 0x002300c2063f8fd6 0xbc008c030818fe3f

def z502 : W := mkw 0xad07b8036e00ec1c 0x02b41ee00db803b0 0xbf03f803fe000e09 0x92fc0fe00ff80038

def z503 : W := mkw 0x18a6048081200000 0x0062981202048000 0x78e707c3c1f00036 0xede39c1f0f07c000

def z504 : W := mkw 0x0001004200108090 0x0000040108004202 0x002300c200300000 0x80008c030800c000

def z505 : W := mkw 0x8807b8024a00ec1c 0x02201ee0092803b0 0x8607f8003800fe3d 0x72181fe000e003f8

def z506 : W := mkw 0x2d0700036400c018 0x00b41c000d900300 0x3f070003fe00f035 0xf0fc1c000ff803c0

def z507 : W := mkw 0x1af646a000000000 0x006bd91a80000000 0xfef7e7f00000000f 0xebfbdf9fc0000000

def z508 : W := mkw 0x4251637218dcbbd2 0x8109458dc86372ef 0xc6f7e7f239fcffff 0xff1bdf9fc8e7f3ff

def z509 : W := mkw 0x4000633008443b42 0x8100018cc02110ed 0xc014e730000cffdf 0x3f00539cc00033ff

def z510 : W := mkw 0xbdafbc8b6e00ec1c 0x0af6bef22db803b0 0xbf2ff8cffe00fe3d 0xf2fcbfe33ff803f8

def z511 : W := mkw 0x0000000000000000 0x0000000000000000 0x00c0000001c00032 0x6403000000070000

def z512 : W := mkw 0x4000211008443b42 0x81000084402110ed 0x000000000000ffc0 0x00000000000003ff

def z513 : W := mkw 0x12f8000091aa0020 0x004be0000246a800 0x06f8000039ff0033 0x741be00000e7fc00

def z514 : W := mkw 0xad07b8036e00ec1c 0x02b41ee00db803b0 0xbf07f803fe007020 0xc2fc1fe00ff801c0

def z515 : W := mkw 0x12f8000091aa0020 0x004be0000246a800 0x38f80003c1ff0032 0xe4e3e0000f07fc00

def z516 : W := mkw 0x0000000000000000 0x0000000000000000 0x010318000000000d 0xa0040c6000000000

def z517 : W := mkw 0xad07b8576e15eedc 0x42b41ee15db857bb 0xbf07f8fffe00fffd 0xfafc1fe3fff803ff

def z518 : W := mkw 0x800020016c006808 0x0200008005b001a0 0x00000001f8007020 0x0000000007e001c0

def z519 : W := mkw 0xa500980126000404 0x0294026004980010 0x0100180006000000 0x0004006000180000

def z520 : W := mkw 0x3ffef6a808002800 0x08fffbdaa02000a0 0xfffffffc3800fe3f 0xfbfffffff0e003f8

def z521 : W := mkw 0x5af747f2d1fcd3db 0x856bdd1fcb47f34f 0x78f707f3c1fcf1f6 0xede3dc1fcf07f3c7

def z522 : W := mkw 0xc2516b337eccff5e 0x830945accdfb33fd 0xc6d4e733ffccffff 0x7f1b539ccfff33ff

def z523 : W := mkw 0x3ffe0581f5ea512b 0x04fff81607d7a944 0x7ec40701f9c07020 0x41fb101c07e701c0

def z524 : W := mkw 0x2500000000000000 0x0094000000000000 0x3f00000000000001 0xe0fc000000000000

def z525 : W := mkw 0x0000001000040240 0x0000000040001009 0x013b18fc000c8fdf 0xbc04ec63f000323f

def z526 : W := mkw 0x2750000134880000 0x009d400004d22000 0x3fd00003ffcc0033 0xf4ff40000fff3000

def z527 : W := mkw 0x080700024000c018 0x00201c0009000300 0x000700000000f004 0x00001c00000003c0

def z528 : W := mkw 0x2759da7e021586d4 0x489d6769f808561b 0x873bf8fe063f8fdf 0xbe1cefe3f818fe3f

def z529 : W := mkw 0x0000004400110080 0x4000000110004402 0x002800cc00330000 0x0000a0033000cc00

def z530 : W := mkw 0xbda7bc836e00ec1c 0x02f69ef20db803b0 0xffe7ffc3fe00fe3f 0xfbff9fff0ff803f8

def z531 : W := mkw 0x18a6058000401102 0x0062981600010044 0x78e707c001c0f1f6 0xede39c1f000703c7

def z532 : W := mkw 0xb7f92803ffaaec3c 0x02dfe4a00ffeabb0 0x3ff80003fffffe33 0xf4ffe0000ffffff8

def z533 : W := mkw 0x000128560a15aed4 0x400004a1582856bb 0x873ff8fe3e3fffff 0xfe1cffe3f8f8ffff

def z534 : W := mkw 0x40002010188c2a40 0x81000080406230a9 0x00000000380c0e00 0x1000000000e03038

def z535 : W := mkw 0x00010856021586d4 0x400004215808561b 0x003b18fc003f8fce 0x0c00ec63f000fe3f

def z536 : W := mkw 0x10a005c081701183 0x044280170205c046 0x78e007c3c1f001f2 0xede3801f0f07c007

def z537 : W := mkw 0x000128020a00ac14 0x000004a0082802b0 0x8707f8023e00fe3d 0xf21c1fe008f803f8

def z538 : W := mkw 0x0000000000000000 0x0000000000000000 0x0138000000000003 0xa004e00000000000

def z539 : W := mkw 0x4250632018c83902 0x8109418c806320e4 0xc6d4e70039cc7033 0x771b539c00e731c0

def z540 : W := mkw 0x0000000000000000 0x0000000000000000 0x013b18fe063f001f 0xbc04ec63f818fc00

def z541 : W := mkw 0x0000000000000000 0x0000000000000000 0x0020000200300012 0xa40080000800c000

def z542 : W := mkw 0x0000010000401102 0x0000000400010044 0x40c4070001c07020 0x4103101c000701c0

def z543 : W := mkw 0x3daf9cce02118494 0x48f6be7338084612 0x392b18ce06330000 0x80e4ac633818cc00

def z544 : W := mkw 0x5af767e2d9f8f99b 0x856bdd9f8b67e3e6 0xfee7e7c3f9f0f1f6 0xeffb9f9f0fe7c3c7

def z545 : W := mkw 0xbdaf9c8b6600c41c 0x0af6be722d980310 0x392b18cfc6000000 0x80e4ac633f180000

def z546 : W := mkw 0x18a704c2c130c099 0x04629c130b04c302 0x382700c3c030f034 0xe0e09c030f00c3c0

def z547 : W := mkw 0x0000004000100080 0x0000000100004002 0x002000c0003001c2 0x0c0080030000c007

def z548 : W := mkw 0x12f94efe021586d4 0x484be53bf808561b 0x41fb1ffe063f8fdf 0xbd07ec7ff818fe3f

def z549 : W := mkw 0x00010857b7bf86f4 0x400004215edefe1b 0x00000003ffff8ff0 0x140000000ffffe3f

def z550 : W := mkw 0x42504230108c0240 0x81094108c0423009 0x00100030000c0000 0x00004000c0003000

def z551 : W := mkw 0x3fff05c2c170d19b 0x04fffc170b05c346 0x7fff07c3c1f0f1f7 0xedfffc1f0f07c3c7

def z552 : W := mkw 0x6758f238188c2a40 0x899d63c8e06230a9 0x8718f83c380c0e09 0x121c63e0f0e03038

def z553 : W := mkw 0x8807b8024a00ec1c 0x02201ee0092803b0 0x8107f8020600fe1d 0xb2041fe0081803f8

def z554 : W := mkw 0xa500b8152e052e44 0x429402e054b814b9 0x8718f83c3e0f0e09 0x121c63e0f0f83c38

def z555 : W := mkw 0x2758d22800000000 0x089d6348a0000000 0x873bf8fc0000000f 0xaa1cefe3f0000000

def z556 : W := mkw 0x42506a341a8d2e44 0xc10941a8d06a34b9 0x8718f83c3e0f0e09 0x121c63e0f0f83c38

def z557 : W := mkw 0x0000000081200000 0x0000000002048000 0x00000003c1f00030 0x040000000f07c000

def z558 : W := mkw 0x3ffed7a8c160510b 0x0cfffb5ea3058144 0xfec4e701c1c07020 0x43fb139c070701c0

def z559 : W := mkw 0x0001080202008414 0x0000042008080210 0x0000000206008e10 0x1000000008180238

def z560 : W := mkw 0x00010052001482d0 0x000004014800520b 0x003300f2003c8fdf 0xbc00cc03c800f23f

def z561 : W := mkw 0x00000001b5aa0020 0x0000000006d6a800 0x00000001f9c00020 0x0000000007e70000

def z562 : W := mkw 0x7ffef7b808443b42 0x89fffbdee02110ed 0xfffffffc0000ffcf 0xebfffffff00003ff

def z563 : W := mkw 0x4250633018cc3b42 0x8109418cc06330ed 0xc614e730380cffcd 0x1b18539cc0e033ff

def z564 : W := mkw 0x10a1004281308090 0x004284010a04c202 0x38e300c3c1f081f6 0xece38c030f07c207

def z565 : W := mkw 0x080704c24010c099 0x04201c1309004302 0x000300c000000000 0x00000c0300000000

def z566 : W := mkw 0x0000000091aa0020 0x000000000246a800 0x0000000001ff0000 0x040000000007fc00

def z567 : W := mkw 0x3fffd6eac130c099 0x0cffff5bab04c302 0xffffffffc030000f 0xebffffffff00c000

def z568 : W := mkw 0x080708564215c6dc 0x40201c215908571b 0x393f18ffc63fffff 0xfce4fc63ff18ffff

def z569 : W := mkw 0x37f90803b7aa8434 0x00dfe4200edeaa10 0x3ffb1803ffff8e3f 0xf4ffec600ffffe38

def z570 : W := mkw 0x480767f24854fbdb 0x85201d9fc92153ef 0xc007e7f00000ffcc 0x0b001f9fc00003ff

def z571 : W := mkw 0x080708024200c41c 0x00201c2009080310 0x39071803c600fe3d 0xf0e41c600f1803f8

def z572 : W := mkw 0x37f80055b5bf02e0 0x40dfe00156d6fc0b 0x3ff800ffffff01f3 0xfcffe003fffffc07

def z573 : W := mkw 0x4250433010cc1342 0x8109410cc043304d 0x40d0073001cc8fdf 0x3d03401cc007323f

def z574 : W := mkw 0x800028012e002c04 0x020000a004b800b0 0x000000003e000e00 0x1000000000f80038

def z575 : W := mkw 0x37f80001a5220020 0x00dfe00006948800 0x3ff80003c6330003 0xe0ffe0000f18cc00

def z576 : W := mkw 0x42506b341acd3f46 0xc10941acd06b34fd 0xc7dcff3c3fcfffff 0x7f1f73fcf0ff3fff

def z577 : W := mkw 0x37f8000000000000 0x00dfe00000000000 0x3ffb18fc0000000f 0xe8ffec63f0000000

def z578 : W := mkw 0x3ffe9489b5aa0020 0x08fffa5226d6a800 0x3ffb18cfffff0033 0xf4ffec633ffffc00

def z579 : W := mkw 0x3ffed7a800401102 0x08fffb5ea0010044 0xfffffffc01c0f1ff 0xeffffffff00703c7

def z580 : W := mkw 0x10a004c081300081 0x044280130204c002 0x002000c000300000 0x000080030000c000

def z581 : W := mkw 0x3daf05c3e572d1bb 0x04f6bc170f95cb46 0x79ef07c3c7f3f1f6 0xede7bc1f0f1fcfc7

def z582 : W := mkw 0x58a767f2c974fbdb 0x85629d9fcb25d3ef 0xf8e7e7f3c1f0fffe 0xefe39f9fcf07c3ff

def z583 : W := mkw 0x4250632018c83902 0x8109418c806320e4 0xc6c4e70039c0f1f6 0x6f1b139c00e703c7

def z584 : W := mkw 0x10a0000000000000 0x0042800000000000 0x38e0000000000002 0xe0e3800000000000

def z585 : W := mkw 0x37f8000091aa0020 0x00dfe0000246a800 0x3ff8000001ff0003 0xe4ffe0000007fc00

def z586 : W := mkw 0x18a60480c1204009 0x0462981203048100 0x38000001c0000000 0x00e0000007000000

def z587 : W := mkw 0x52f067f099fc3bc3 0x854bc19fc267f0ef 0xc6f4e7f039fcffff 0x7f1bd39fc0e7f3ff

def z588 : W := mkw 0x0806948800000000 0x08201a5220000000 0x000318cc00000000 0x00000c6330000000

def z589 : W := mkw 0x00000054001502c0 0x400000015000540b 0x003800fc003f8fdf 0x3c00e003f000fe3f

def z590 : W := mkw 0x10a005d4817513c3 0x444280175205d44f 0x40f807fc01ff01c2 0x0d03e01ff007fc07

def z591 : W := mkw 0x3ffed6a800000000 0x08fffb5aa0000000 0xfffce70000000003 0xe3fff39c00000000

def z592 : W := mkw 0xaf57b8037e88ec1c 0x02bd5ee00dfa23b0 0xbfd7f803ffccfe3f 0xf6ff5fe00fff33f8

def z593 : W := mkw 0x3ffed6a800000000 0x08fffb5aa0000000 0xfed4e7300000000f 0x6bfb539cc0000000

def z594 : W := mkw 0x4250433010cc1342 0x8109410cc043304d 0xc6d4e73001cc01cf 0x6f1b539cc0073007

def z595 : W := mkw 0x0000000000000000 0x0000000000000000 0x0600000038000031 0x7018000000e00000

def z596 : W := mkw 0x2758da3c02050644 0x489d6368f0081419 0x8718f83c060f0e09 0x121c63e0f0183c38

def z597 : W := mkw 0xad0798036600c41c 0x02b41e600d980310 0x39031803c6008e1d 0xb0e40c600f180238

def z598 : W := mkw 0x18a705c2c170d19b 0x04629c170b05c346 0x782707c3c030f1c4 0x89e09c1f0f00c3c7

def z599 : W := mkw 0xa758b8013e8a2c24 0x029d62e004fa28b0 0x8718f8003e0f0e09 0x121c63e000f83c38

def z600 : W := mkw 0x0000011000441342 0x000000044001104d 0x40d4073001ccffff 0x7d03501cc00733ff

def z601 : W := mkw 0x0807defe021586d4 0x48201f7bf808561b 0xc007fffc00008fcc 0x0b001ffff000023f

def z602 : W := mkw 0x3fff0003f5aac038 0x00fffc000fd6ab00 0x3fff0003fffff037 0xf4fffc000fffffc0

def z603 : W := mkw 0x12f846a800000000 0x084be11aa0000000 0x41fb1ffc0000000f 0xa907ec7ff0000000

def z604 : W := mkw 0x8807bdc24a50fd9f 0x06201ef7092943f6 0xc007ffc00000ffcc 0x0b001fff000003ff

def z605 : W := mkw 0x080705c2c170d19b 0x04201c170b05c346 0x400707c3c1f0f1f4 0x0d001c1f0f07c3c7

def z606 : W := mkw 0x2508900800000000 0x0894224020000000 0x0108180c00000000 0x0004206030000000

def z607 : W := mkw 0x2f5ed22800000000 0x08bd7b48a0000000 0xbf1ff83c0000000d 0xe2fc7fe0f0000000

def z608 : W := mkw 0x77f8633018cc3b42 0x81dfe18cc06330ed 0xfffce73039ccffff 0xfffff39cc0e733ff

def z609 : W := mkw 0x4000211018cc3b42 0x81000084406330ed 0x8604e00039ccfffd 0x7618138000e733ff

def z610 : W := mkw 0x00000001b5aa0020 0x0000000006d6a800 0x01380003ffff0033 0xb404e0000ffffc00

def z611 : W := mkw 0x12f8000091aa0020 0x004be0000246a800 0x01f8000207ff0013 0xb407e000081ffc00

def z612 : W := mkw 0xad0798036600c41c 0x02b41e600d980310 0x39071803c600f034 0xe0e41c600f1803c0

def z613 : W := mkw 0x8807b8564a15eedc 0x42201ee1592857bb 0x813ff8fe063fffdf 0xbe04ffe3f818ffff

def z614 : W := mkw 0x37f8000124000000 0x00dfe00004900000 0x3ff80003fe000033 0xf0ffe0000ff80000

def z615 : W := mkw 0x0250422000000000 0x0009410880000000 0xc6c4e70000000000 0x431b139c00000000

def z616 : W := mkw 0x27590857369f86f4 0x409d64215cda7e1b 0x073b18fe3e3f8fdf 0xbc1cec63f8f8fe3f

def z617 : W := mkw 0x37f8000010880000 0x00dfe00000422000 0x3ff8000039cc0033 0xf4ffe00000e73000

def z618 : W := mkw 0x3dae948800000000 0x08f6ba5220000000 0x393b18fc0000000f 0xa8e4ec63f0000000

def z619 : W := mkw 0x4250432010c81102 0x8109410c80432044 0x40c0070001c00000 0x0103001c00070000

def z620 : W := mkw 0x00010856021586d4 0x400004215808561b 0x0118183e063f8fd9 0x14046060f818fe3f

def z621 : W := mkw 0x37f80001b5aa0020 0x00dfe00006d6a800 0x3fc00003ffc00031 0xf0ff00000fff0000

def z622 : W := mkw 0x18a725c2c970f99b 0x04629c970b25c3e6 0xfee7e7c3f9f0ffff 0xfffb9f9f0fe7c3ff

def z623 : W := mkw 0xad07b8036e00ec1c 0x02b41ee00db803b0 0x8707f8003e00fe0d 0x121c1fe000f803f8

def z624 : W := mkw 0x3fffd7ea4050d19b 0x0cffff5fa9014346 0xfffffffc0000f1cf 0xebfffffff00003c7

def z625 : W := mkw 0x800108036600c41c 0x020004200d980310 0x00000003c6000000 0x000000000f180000

def z626 : W := mkw 0x12f805c091fa11a3 0x044be0170247e846 0x40f807c001ff01c2 0x0d03e01f0007fc07

def z627 : W := mkw 0x35a80001a5220020 0x00d6a00006948800 0x38000001c0000000 0x00e0000007000000

def z628 : W := mkw 0x42516b761addbfd6 0xc10945add86b76ff 0xc6d4e7323fffffff 0x7f1b539cc8ffffff

def z629 : W := mkw 0x1afe46a800000000 0x086bf91aa0000000 0x78ff07fc00000006 0xe9e3fc1ff0000000

def z630 : W := mkw 0x10a8000081220020 0x0042a00002048800 0x0028000000330000 0x0000a0000000cc00

def z631 : W := mkw 0xbffeb001fdaa6828 0x02fffac007f6a9a0 0xbec4e001f9c07020 0x42fb138007e701c0

def z632 : W := mkw 0x12f9085693bf86f4 0x404be4215a4efe1b 0x01fb18fe07ff8fdf 0xbc07ec63f81ffe3f

def z633 : W := mkw 0x3fffdffec375d7df 0x4cffff7ffb0dd75f 0xffffffffc7ffffff 0xffffffffff1fffff

def z634 : W := mkw 0xad07b8176e05ee5c 0x42b41ee05db817b9 0xbf1ff83ffe0ffe3d 0xf2fc7fe0fff83ff8

def z635 : W := mkw 0x00010856021586d4 0x400004215808561b 0x010318fe06008fdd 0xb8040c63f818023f

def z636 : W := mkw 0x3fffdefe021586d4 0x48ffff7bf808561b 0xfffffffc00008fcf 0xebfffffff000023f

def z637 : W := mkw 0x18a704c200108090 0x00629c1308004202 0x78e707c2003081d6 0xede39c1f0800c207

def z638 : W := mkw 0x00010042c130c099 0x040004010b04c302 0x00000003c0300000 0x000000000f00c000

def z639 : W := mkw 0x5af667a0d9e8790b 0x856bd99e8367a1e4 0xfec4e701f9c07020 0x43fb139c07e701c0

def z640 : W := mkw 0x8807b8036e00ec1c 0x02201ee00db803b0 0x8007f803fe00fe3c 0x12001fe00ff803f8

def z641 : W := mkw 0x5af667b018cc3b42 0x816bd99ec06330ed 0xfef7e7f039ccffff 0xfffbdf9fc0e733ff

def z642 : W := mkw 0x00000054001502c0 0x400000015000540b 0x013b18fc003f01cf 0xac04ec63f000fc07

def z643 : W := mkw 0x3fff0dd7f7ffd7ff 0x44fffc375fdfff5f 0x7fff1fffffffffff 0xfdfffc7fffffffff

def z644 : W := mkw 0x37f80815b7af0664 0x40dfe02056debc19 0x3ff8183fffff0e3b 0xf4ffe060fffffc38

def z645 : W := mkw 0x3ffed6a800000000 0x08fffb5aa0000000 0xffc7ff000000000d 0xe3ff1ffc00000000

def z646 : W := mkw 0xbffef6a96c006808 0x0afffbdaa5b001a0 0xfffffffdf800702f 0xebfffffff7e001c0

def z647 : W := mkw 0xbffefea92e002c04 0x0afffbfaa4b800b0 0xfffffffc3e000e0f 0xfbfffffff0f80038

def z648 : W := mkw 0x4806f7b808443b42 0x89201bdee02110ed 0xc007fffc0000ffcc 0x0b001ffff00003ff

def z649 : W := mkw 0x08070dd64255d7df 0x44201c375909575f 0x40071ffc0000ffcc 0x09001c7ff00003ff

def z650 : W := mkw 0x0250423000040240 0x00094108c0001009 0xc6d4e730000c8fdf 0x7f1b539cc000323f

def z651 : W := mkw 0x800128036e00ec1c 0x020004a00db803b0 0x01031803fe00fe3d 0xb0040c600ff803f8

def z652 : W := mkw 0x37f846a800000000 0x08dfe11aa0000000 0x7ff807fc00000003 0xe9ffe01ff0000000

def z653 : W := mkw 0x77f84331b5ee1362 0x81dfe10cc6d7b84d 0x7ff80733ffff01f3 0xfdffe01ccffffc07

def z654 : W := mkw 0x3ffed6a800000000 0x08fffb5aa0000000 0xfefce7fc00000002 0x4bfbf39ff0000000

def z655 : W := mkw 0xfffffb33ffeeff7e 0x83ffffeccfffbbfd 0xffffff33ffffffff 0xfffffffccfffffff

def z656 : W := mkw 0x37f90143f5fad1bb 0x04dfe4050fd7eb46 0x3ff80003fffff1f3 0xf4ffe0000fffffc7

def z657 : W := mkw 0x37f8d6a800000000 0x08dfe35aa0000000 0xc7f8fffc0000000b 0x0b1fe3fff0000000

def z658 : W := mkw 0x0001081602058654 0x4000042058081619 0x011b183e060f8e1d 0xb0046c60f8183e38

def z659 : W := mkw 0xef56f3217cc8790a 0x83bd5bcc85f321e4 0xfec4e701f9c07020 0x43fb139c07e701c0

def z660 : W := mkw 0x10a0000081200000 0x0042800002048000 0x00e0000001f00002 0x040380000007c000

def z661 : W := mkw 0x27580001b5aa0020 0x009d600006d6a800 0x07180003ffff0031 0x141c60000ffffc00

def z662 : W := mkw 0x12f0000091a80000 0x004bc0000246a000 0x3ef00003f9fc0033 0xf4fbc0000fe7f000

def z663 : W := mkw 0x27580001348a0020 0x009d600004d22800 0x07d800003fcf0033 0x741f600000ff3c00

def z664 : W := mkw 0x00010856021586d4 0x400004215808561b 0x011b18fc060f8fcd 0x18046c63f0183e3f

def z665 : W := mkw 0x37f8000000000000 0x00dfe00000000000 0x3ff80002063f0013 0xf4ffe0000818fc00

def z666 : W := mkw 0x0000200008002800 0x00000080002000a0 0x8004e0000000fe0c 0x02001380000003f8

def z667 : W := mkw 0x7ffef7a818c83902 0x89fffbdea06320e4 0xfffffffc39c0702f 0xebfffffff0e701c0

def z668 : W := mkw 0xad0798576615c6dc 0x42b41e615d98571b 0x393b18ffc63f8fdf 0xbce4ec63ff18fe3f

def z669 : W := mkw 0x10a0000081200000 0x0042800002048000 0x39f80003c7ff0033 0xf4e7e0000f1ffc00

def z670 : W := mkw 0x0000000000000000 0x0000000000000000 0x0100000206000011 0xb004000008180000

def z671 : W := mkw 0x18a60580c160510b 0x0462981603058144 0x78e707c1c1c07026 0xe9e39c1f070701c0

def z672 : W := mkw 0x42506230188c2a40 0x81094188c06230a9 0xc6d4e730380c0e0f 0x7b1b539cc0e03038

def z673 : W := mkw 0x4250633018cc3b42 0x8109418cc06330ed 0xc6d0e73039cc0fcb 0x1f1b439cc0e7303f

def z674 : W := mkw 0x0250010010c81102 0x0009400400432044 0x46d4070039ccf1f7 0x7d1b501c00e733c7

def z675 : W := mkw 0xad07b943ef70fd9f 0x06b41ee50fbdc3f6 0xbf07f803fff0fffd 0xf6fc1fe00fffc3ff

def z676 : W := mkw 0x7ffef7a818c83902 0x89fffbdea06320e4 0xfec4e70039c07020 0x43fb139c00e701c0

def z677 : W := mkw 0x77f96b77bfffbff6 0xc1dfe5addefffeff 0xffffffffffffffff 0xffffffffffffffff

def z678 : W := mkw 0x37f8d22800000000 0x08dfe348a0000000 0xbff8f83c0000000b 0xe2ffe3e0f0000000

def z679 : W := mkw 0x6f56f33018cc3b42 0x81bd5bccc06330ed 0xffd7ff3039ccffff 0xffff5ffcc0e733ff

def z680 : W := mkw 0x4000623008042a40 0x81000188c02010a9 0x8000e03000000e08 0x02000380c0000038

def z681 : W := mkw 0x02580000108a0020 0x0009600000422800 0x00180000000f0000 0x0000600000003c00

def z682 : W := mkw 0xca57fb325accff5e 0x83295fecc96b33fd 0xc6d7ff3039ccffff 0x7f1b5ffcc0e733ff

def z683 : W := mkw 0x0001081202048654 0x0000042048081219 0x01131832060c8fdf 0xbc044c60c818323f

def z684 : W := mkw 0xbffef6a96c006808 0x0afffbdaa5b001a0 0xfec4e701f8007020 0x43fb139c07e001c0

def z685 : W := mkw 0xbda79dc3e770d59f 0x06f69e770f9dc356 0x79e71fc3c7f0f1f6 0xede79c7f0f1fc3c7

def z686 : W := mkw 0x3dae948800000000 0x08f6ba5220000000 0x3800000000000000 0x00e0000000000000

def z687 : W := mkw 0x4a5767f258dcfbdb 0x85295d9fc96373ef 0xc6d7e7f039ccffff 0x7f1b5f9fc0e733ff

def z688 : W := mkw 0x77f82111bdee3b62 0x81dfe08446f7b8ed 0x3ff80003fffffff3 0xf4ffe0000fffffff

def z689 : W := mkw 0x37f80001b5aa0020 0x00dfe00006d6a800 0x3ff80001f9c00023 0xe0ffe00007e70000

def z690 : W := mkw 0x0001084602118494 0x4000042118084612 0x0000000206330000 0x000000000818cc00

def z691 : W := mkw 0x880728036e00ec1c 0x02201ca00db803b0 0x38070003fe00fe34 0xf0e01c000ff803f8

def z692 : W := mkw 0x1aff05c2d1fad1bb 0x046bfc170b47eb46 0x78ff07c3c1fff1f6 0xede3fc1f0f07ffc7

def z693 : W := mkw 0x4250437410dd13c2 0xc109410dd043744f 0x40f807fc01ff01c2 0x0d03e01ff007fc07

def z694 : W := mkw 0x10a10856833586d4 0x404284215a0cd61b 0x39fb18ffc7ff8fff 0xfce7ec63ff1ffe3f

def z695 : W := mkw 0x3ffed6a800000000 0x08fffb5aa0000000 0xbf3bf8fc00000009 0x82fcefe3f0000000

def z696 : W := mkw 0x4250633018cc3b42 0x8109418cc06330ed 0xc0d4e73001ccffce 0x0f03539cc00733ff

def z697 : W := mkw 0x3fffdeee02118494 0x48ffff7bb8084612 0xfffffffe0633000f 0xebfffffff818cc00

def z698 : W := mkw 0x4000211018cc3b42 0x81000084406330ed 0x40c4070039ccfff6 0x7d03101c00e733ff

def z699 : W := mkw 0xad0798036600c41c 0x02b41e600d980310 0x3f031803fe000031 0xf0fc0c600ff80000

def z700 : W := mkw 0x52f867b818cc3b42 0x894be19ee06330ed 0xc6fce7fc39ccffff 0x7f1bf39ff0e733ff

def z701 : W := mkw 0x2d079856021586d4 0x40b41e615808561b 0xbf3ff8fe063f8fdf 0xfefcffe3f818fe3f

def z702 : W := mkw 0x00010856021586d4 0x400004215808561b 0x003800fe063f8fd2 0x1c00e003f818fe3f

def z703 : W := mkw 0x18a705c2c170d19b 0x04629c170b05c346 0x78e707c3c1f07020 0xc1e39c1f0f07c1c0

def z704 : W := mkw 0x10a005c081701183 0x044280170205c046 0x40e407c001f0f1f6 0x6d03901f0007c3c7

def z705 : W := mkw 0x00000100c160510b 0x0400000403058144 0x00000001c1c07020 0x00000000070701c0

def z706 : W := mkw 0x3fff04c3f5bac0b9 0x04fffc130fd6eb02 0x3ffb00c3ffff0033 0xf4ffec030ffffc00

def z707 : W := mkw 0x37f846a9b5aa0020 0x08dfe11aa6d6a800 0x7ff80703ffff0033 0xf5ffe01c0ffffc00

def z708 : W := mkw 0x0806d6a800000000 0x08201b5aa0000000 0xc12ffffc0000000c 0x8b04bffff0000000

def z709 : W := mkw 0x27580001b5aa0020 0x009d600006d6a800 0x3f180003ffff0031 0xf4fc60000ffffc00

def z710 : W := mkw 0x5af766f2d9bcead9 0x856bdd9bcb66f3ab 0xbe33e0f3f83c0e09 0x92f8cf83cfe0f038

def z711 : W := mkw 0x3da6948000000000 0x00f69a5200000000 0xfffffffc0000000f 0xebfffffff0000000

def z712 : W := mkw 0x18a705c2c170d19b 0x04629c170b05c346 0x78c40703c1f0f1f6 0x6de3101c0f07c3c7

def z713 : W := mkw 0x0000422000000000 0x0000010880000000 0xc007fffc0000000c 0x0b001ffff0000000

def z714 : W := mkw 0xbdaf9ccbe730c49d 0x0ef6be732f9cc312 0x392b18cfc6300000 0x80e4ac633f18c000

def z715 : W := mkw 0x3daed6a800000000 0x08f6bb5aa0000000 0xff2ffffc0000000d 0xebfcbffff0000000

def z716 : W := mkw 0x27500001b5aa0020 0x009d400006d6a800 0x3fd00003ffff0033 0xf4ff40000ffffc00

def z717 : W := mkw 0x18a705c2c170d19b 0x04629c170b05c346 0x78f707f3c1f0f1ff 0xede3dc1fcf07c3c7

def z718 : W := mkw 0x2f5ed6a9348a0020 0x08bd7b5aa4d22800 0xc71ffffc3e0f000d 0x1b1c7ffff0f83c00

def z719 : W := mkw 0x3ffed6a840004008 0x08fffb5aa1000100 0xfffffffdc000702f 0xebfffffff70001c0

def z720 : W := mkw 0x18a705c2c170d19b 0x04629c170b05c346 0x79ef07c3c7f3f1f6 0xede7bc1f0f1fcfc7

def z721 : W := mkw 0x4250633018cc3b42 0x8109418cc06330ed 0xc6fce7fc39ccffff 0x7f1bf39ff0e733ff

def z722 : W := mkw 0x42516b661ad9bd96 0xc10945ad986b66f6 0xc7efffce3ff37020 0xc31fbfff38ffcdc0

def z723 : W := mkw 0x3ffed6a881200000 0x08fffb5aa2048000 0xffffffffc030000f 0xebffffffff00c000

def z724 : W := mkw 0x3ffed6a924000000 0x08fffb5aa4900000 0xfffffffdf800002f 0xebfffffff7e00000

def z725 : W := mkw 0x7daeb59818cc3b42 0x89f6bad6606330ed 0x392b18cc39ccfff0 0x94e4ac6330e733ff

def z726 : W := mkw 0x18a705c2c170d19b 0x04629c170b05c346 0x78c707c1c1c0f1f6 0x6de31c1f070703c7

def z727 : W := mkw 0x3ffed6a800000000 0x08fffb5aa0000000 0xfffffffc000c001f 0xfffffffff0003000

def z728 : W := mkw 0x37f80001b5aa0020 0x00dfe00006d6a800 0x3ffc0003fffff037 0xf4fff0000fffffc0

def z729 : W := mkw 0x1afed6a891aa0020 0x086bfb5aa246a800 0xc0fffffc01ff000e 0x0f03fffff007fc00

def z730 : W := mkw 0x3ffed6a9b5aa0020 0x08fffb5aa6d6a800 0xfec7fffdf9c0002c 0x4bfb1ffff7e70000

def z731 : W := mkw 0x3ffed6a9a5220020 0x08fffb5aa6948800 0xffffffffc7f3003f 0xefffffffff1fcc00

def z732 : W := mkw 0x3ffed6a800000000 0x08fffb5aa0000000 0xfffffffc060f000f 0xfbfffffff0183c00

def z733 : W := mkw 0x4250633018cc3b42 0x8109418cc06330ed 0xc6c4e70039ccfffd 0x771b139c00e733ff

def z734 : W := mkw 0x0a56d6a810880000 0x08295b5aa0422000 0xc6d7fffc39cc003f 0x7f1b5ffff0e73000

def z735 : W := mkw 0x25000001b5aa0020 0x0094000006d6a800 0x39000003ffff0030 0x94e400000ffffc00

def z736 : W := mkw 0x18a60d94c365574f 0x44629836530d955d 0x79dc1f3dc7cf7e29 0x51e7707cf71f3df8

def z737 : W := mkw 0x3ffed6a891aa0020 0x08fffb5aa246a800 0xffffffffc1ff003f 0xefffffffff07fc00

def z738 : W := mkw 0x3fffdefe021586d4 0x48ffff7bf808561b 0xfec4e702063f8fd0 0x57fb139c0818fe3f

def z739 : W := mkw 0x18a605c0c170518b 0x046298170305c146 0x78e707c1c1f071e6 0xede39c1f0707c1c7

def z740 : W := mkw 0x37f84221b5aa0020 0x00dfe10886d6a800 0xffffffffffff003f 0xfffffffffffffc00

def z741 : W := mkw 0x18a705c2c170d19b 0x04629c170b05c346 0x78e707c3c7fff1f6 0xfde39c1f0f1fffc7

def z742 : W := mkw 0x18a705c2c170d19b 0x04629c170b05c346 0x78e707c3c1f0f1f0 0xc5e39c1f0f07c3c7

def z743 : W := mkw 0xbdaf9cc3e732c4bd 0x06f6be730f9ccb12 0x392b18c3c6330000 0x80e4ac630f18cc00

def z744 : W := mkw 0x1afed6a800000000 0x086bfb5aa0000000 0xc6fffffc0000000f 0x6b1bfffff0000000

def z745 : W := mkw 0x4250633018cc3b42 0x8109418cc06330ed 0xc6f4e73239fcffff 0xff1bd39cc8e7f3ff

def z746 : W := mkw 0xad07b8476e11ec9c 0x42b41ee11db847b2 0xbf07f803fe33fe3d 0xf2fc1fe00ff8cff8

def z747 : W := mkw 0x18a70582c160d11b 0x04629c160b058344 0x78c70703c1c0f1f6 0xede31c1c0f0703c7

def z748 : W := mkw 0xad06b0556c156ac8 0x42b41ac155b055ab 0xbe3ce0fdf83f71e2 0x4ef8f383f7e0fdc7

def z749 : W := mkw 0x3da6d6a800000000 0x08f69b5aa0000000 0xffe7fffc0000000f 0xebff9ffff0000000

def z750 : W := mkw 0x3ffed6a9b5aa0020 0x08fffb5aa6d6a800 0xffffffffffc0003f 0xfbffffffffff0000

def z751 : W := mkw 0xb5a0bdc1af703d87 0x06d682f706bdc0f6 0xc7e0ffc03ff00fcb 0x1f1f83ff00ffc03f

def z752 : W := mkw 0x52f047b091ec1343 0x854bc11ec247b04d 0x40d0073001cc01c2 0x0d03401cc0073007

def z753 : W := mkw 0x4250633018cc3b42 0x8109418cc06330ed 0xc6c4e73039ccfffc 0x5f1b139cc0e733ff

def z754 : W := mkw 0x4258633818cc3b42 0x8909618ce06330ed 0xc6dce73c39ccffff 0x7f1b739cf0e733ff

def z755 : W := mkw 0x2f5ed6a800000000 0x08bd7b5aa0000000 0xc73ffffc0000000f 0xab1cfffff0000000

def z756 : W := mkw 0xad07b8036e00ec1c 0x02b41ee00db803b0 0xbf3ff8fffe3ffe3f 0xfefcffe3fff8fff8

def z757 : W := mkw 0x4250632018c83902 0x8109418c806320e4 0xc6c4e70039c0ffff 0x7f1b139c00e703ff

def z758 : W := mkw 0x3ffed6a9348a0020 0x08fffb5aa4d22800 0xfffffffe3e3f001f 0xfffffffff8f8fc00

def z759 : W := mkw 0xad07b8036e00ec1c 0x02b41ee00db803b0 0xbf2ff8cffe00fe3d 0xf2fcbfe33ff803f8

def z760 : W := mkw 0x3ffed6a924000000 0x08fffb5aa4900000 0xfffffffc3e00000f 0xfbfffffff0f80000

def z761 : W := mkw 0x2d06d6a924000000 0x08b41b5aa4900000 0xff07fffffe00003d 0xfbfc1ffffff80000

def z762 : W := mkw 0x37f8d229b5aa0020 0x08dfe348a6d6a800 0xbff8e003ffff0033 0xf6ffe3800ffffc00

def z763 : W := mkw 0x18a705c2c170d19b 0x04629c170b05c346 0x78e71fffc1f0f1fe 0xede39c7fff07c3c7

def z764 : W := mkw 0x2f5f05c374dad1bb 0x04bd7c170dd36b46 0x471f07c03e0ff1c5 0x191c7c1f00f83fc7

def z765 : W := mkw 0x00010856021586d4 0x400004215808561b 0x41ff1ffe063f8fdf 0xfd07fc7ff818fe3f

def z766 : W := mkw 0x18aed6a800000000 0x0862bb5aa0000000 0xc02ffffc0000000c 0x0b00bffff0000000

def z767 : W := mkw 0x37f80001b5aa0020 0x00dfe00006d6a800 0x3ff80003ffff0021 0xd0ffe0000ffffc00

def z768 : W := mkw 0xad06b8016e006c0c 0x02b41ae005b801b0 0xbf04f801fe00fe3d 0x72fc13e007f803f8

def z769 : W := mkw 0x3ffed6a9b5aa0020 0x08fffb5aa6d6a800 0xfffffffff9f0003f 0xefffffffffe7c000

def z770 : W := mkw 0x3ffed6a800000000 0x08fffb5aa0000000 0xfefffffc0000000e 0x4bfbfffff0000000

def z771 : W := mkw 0x18a705c2c170d19b 0x04629c170b05c346 0x78c40701c1c0f1e0 0x41e3101c070703c7

def z772 : W := mkw 0x4250633018cc3b42 0x8109418cc06330ed 0xc7dce7303fcfffff 0x7f1f739cc0ff3fff

def z773 : W := mkw 0xad07b8036e00ec1c 0x02b41ee00db803b0 0xbf07f801f800fe2d 0xe2fc1fe007e003f8

def z774 : W := mkw 0x3ffed6a810880000 0x08fffb5aa0422000 0xfffffffc380c000f 0xfbfffffff0e03000

def z775 : W := mkw 0x3ffed6a9b5aa0020 0x08fffb5aa6d6a800 0xfffffffffff3002f 0xebffffffffffcc00

def z776 : W := mkw 0x400129561addbfd6 0xc10004a5586b76ff 0x0000000039ccfff0 0x1400000000e733ff

def z777 : W := mkw 0x3ffed6a891aa0020 0x08fffb5aa246a800 0xfffffffe07ff001f 0xfffffffff81ffc00

def z778 : W := mkw 0xad07b8036e00ec1c 0x02b41ee00db803b0 0xbf07f8fffe00fe3d 0xfafc1fe3fff803f8

def z779 : W := mkw 0xad07b8436e10ec9c 0x02b41ee10db843b2 0xbf3ff8fffe30ffff 0xfefcffe3fff8c3ff

def z780 : W := mkw 0x3ffed6a9348a0020 0x08fffb5aa4d22800 0xfffffffc3fcf003f 0xfffffffff0ff3c00

def z781 : W := mkw 0x8807bdd64a55ffdf 0x46201ef7592957ff 0xc007fffc0000ffcc 0x0b001ffff00003ff

def z782 : W := mkw 0x2d06b0012c002800 0x00b41ac004b000a0 0xbf07f803fe00fe3d 0xf2fc1fe00ff803f8

def z783 : W := mkw 0x37f80001b5aa0020 0x00dfe00006d6a800 0x3fe80003ffff0030 0xd4ffa0000ffffc00

def z784 : W := mkw 0x37f80001b5aa0020 0x00dfe00006d6a800 0x3ff80003ffff0003 0x94ffe0000ffffc00

def z785 : W := mkw 0x18a795c2c170d19b 0x04629e570b05c346 0xf8e7ffc3c1f0f1fe 0xefe39fff0f07c3c7

def z786 : W := mkw 0x2d06d6a800000000 0x08b41b5aa0000000 0xfe07fffc0000000c 0x4bf81ffff0000000

def z787 : W := mkw 0x00010856021586d4 0x400004215808561b 0x013b18fe063f0fcb 0x9c04ec63f818fc3f

def z788 : W := mkw 0x1afed6a800000000 0x086bfb5aa0000000 0xc1fffffc0000000f 0xab07fffff0000000

def z789 : W := mkw 0xbda79cc7e731c49d 0x46f69e731f9cc712 0x392b18cfc6330000 0x80e4ac633f18cc00

def z790 : W := mkw 0x4250633018cc3b42 0x8109418cc06330ed 0xc7dcff3c39ccffff 0x7f1f73fcf0e733ff

def z791 : W := mkw 0x18a705c2c170d19b 0x04629c170b05c346 0x79ff1fffc7fff1ff 0xfde7fc7fff1fffc7

def z792 : W := mkw 0x18a70dc6c371d59f 0x44629c371b0dc756 0x79ff1fcfc7fff1f7 0xfde7fc7f3f1fffc7

def z793 : W := mkw 0xad06b8016e006c0c 0x02b41ae005b801b0 0xbf04f803fe007e39 0xf2fc13e00ff801f8

def z794 : W := mkw 0x3ffed6a9b5aa0020 0x08fffb5aa6d6a800 0xfffffffdf9ff002f 0xeffffffff7e7fc00

def z795 : W := mkw 0x92f96eab6e00ec1c 0x0a4be5baadb803b0 0x40f807fffe00fe32 0x1903e01ffff803f8

def z796 : W := mkw 0x3ffed6a800000000 0x08fffb5aa0000000 0xf9fffffc0000000e 0x8be7fffff0000000

def z797 : W := mkw 0x3ffed6a800000000 0x08fffb5aa0000000 0xc7fffffc0000000f 0x0b1ffffff0000000

def z798 : W := mkw 0xef57db3376ccd75e 0x83bd5f6ccddb335d 0x79d31f33c7cc01c2 0x8de74c7ccf1f3007

def z799 : W := mkw 0x3ffed6a800000000 0x08fffb5aa0000000 0xfffffffc000081df 0xeffffffff0000207

def z800 : W := mkw 0x2f5ed6a800000000 0x08bd7b5aa0000000 0xff1ffffc0000000d 0xebfc7ffff0000000

def z801 : W := mkw 0x77f92957bfffbff6 0xc1dfe4a55efffeff 0x3ff80003fffffff3 0xf4ffe0000fffffff

def z802 : W := mkw 0x2f56d6a800000000 0x08bd5b5aa0000000 0xffd7fffc0000000f 0xebff5ffff0000000

def z803 : W := mkw 0x4250633018cc3b42 0x8109418cc06330ed 0xc6c4e70039ccfff6 0x7f1b139c00e733ff

def z804 : W := mkw 0x37f846a9b5aa0020 0x08dfe11aa6d6a800 0x7ffb1fffffff003f 0xfdffec7ffffffc00

def z805 : W := mkw 0xad07b8036e00ec1c 0x02b41ee00db803b0 0xbf2ff803fe33fe3d 0xf2fcbfe00ff8cff8

def z806 : W := mkw 0x37f80001b5aa0020 0x00dfe00006d6a800 0x3ff80003ffff0022 0xc4ffe0000ffffc00

def z807 : W := mkw 0xad07b8476e11ec9c 0x42b41ee11db847b2 0xbf3ff8cffe3ffe3f 0xf6fcffe33ff8fff8

def z808 : W := mkw 0x35a80001b5aa0020 0x00d6a00006d6a800 0x3f280003ffff0031 0xf4fca0000ffffc00

def z809 : W := mkw 0x35a00001b5aa0020 0x00d6800006d6a800 0x3fe00003ffff0033 0xf4ff80000ffffc00

def z810 : W := mkw 0x3ffed6a800000000 0x08fffb5aa0000000 0xffdffffc0000000d 0x4bff7ffff0000000

def z811 : W := mkw 0x37f80001b5aa0020 0x00dfe00006d6a800 0x3ffb18cfffff0033 0xf4ffec633ffffc00

def z812 : W := mkw 0x3ffed6a800000000 0x08fffb5aa0000000 0xfffffffc3800003f 0xfbfffffff0e00000

def z813 : W := mkw 0x9affb802dbaaec3c 0x026bfee00b6eabb0 0x80fff80001fffe0e 0x0603ffe00007fff8

def z814 : W := mkw 0x3ffed6a9b5aa0020 0x08fffb5aa6d6a800 0xffffffffc7ff000f 0xefffffffff1ffc00

def z815 : W := mkw 0xad07b8036e00ec1c 0x02b41ee00db803b0 0xbf3ff803fe00fe3f 0xf2fcffe00ff803f8

def z816 : W := mkw 0x3ffed6a810880000 0x08fffb5aa0422000 0xfffffffc01cc000f 0xeffffffff0073000

def z817 : W := mkw 0x2d06d6a800000000 0x08b41b5aa0000000 0xf907fffc0000000c 0x8be41ffff0000000

def z818 : W := mkw 0x75a86331ad663b62 0x81d6a18cc6b598ed 0xf92ce733c633ffcc 0x8be4b39ccf18cfff

def z819 : W := mkw 0x3ffed6a9b5aa0020 0x08fffb5aa6d6a800 0xfffffffc3fff000f 0xfffffffff0fffc00

def z820 : W := mkw 0x18a705c2c170d19b 0x04629c170b05c346 0x78e707c3c1f0f1c6 0x8de39c1f0f07c3c7

def z821 : W := mkw 0x0806200048006808 0x00201880012001a0 0xbe04e001f800fe3d 0x72f8138007e003f8

def z822 : W := mkw 0x18a705c2c170d19b 0x04629c170b05c346 0x78c707c3c1f0f1f4 0x4de31c1f0f07c3c7

def z823 : W := mkw 0x37f80001b5aa0020 0x00dfe00006d6a800 0x3ff80003ffff8e3f 0xf4ffe0000ffffe38

def z824 : W := mkw 0xe758fa393e8c2e44 0x8b9d63e8e4fa30b9 0x8718f83c3e0c0e09 0x121c63e0f0f83038

def z825 : W := mkw 0x37f90857b7bf86f4 0x40dfe4215edefe1b 0x3ec318fdf9c08fec 0x48fb0c63f7e7023f

def z826 : W := mkw 0x3ffed6a800000000 0x08fffb5aa0000000 0xfed7fffc0000000f 0x6bfb5ffff0000000

def z827 : W := mkw 0x18a705c2c170d19b 0x04629c170b05c346 0x78ff07c3c1fff1f6 0xede3fc1f0f07ffc7

def z828 : W := mkw 0x18a70dc6c371d59f 0x44629c371b0dc756 0x79ef1fcfc7f3ffff 0xfde7bc7f3f1fcfff

def z829 : W := mkw 0x18a605c0c170518b 0x046298170305c146 0x78c40701c1f071e0 0x45e3101c0707c1c7

def z830 : W := mkw 0x18a705c2c170d19b 0x04629c170b05c346 0x78c707c3c1c0f1f4 0xe9e31c1f0f0703c7

def z831 : W := mkw 0xad07b8036e00ec1c 0x02b41ee00db803b0 0xbf27f803fe30fe3f 0xf6fc9fe00ff8c3f8

def z832 : W := mkw 0x37f84221b5aa0020 0x00dfe10886d6a800 0xbff8e033ffff003b 0xf6ffe380cffffc00

def z833 : W := mkw 0xad07b8476e11ec9c 0x42b41ee11db847b2 0xbf3ff8fffe33fe3f 0xfafcffe3fff8cff8

def z834 : W := mkw 0xad07b8076e01ec1c 0x42b41ee01db807b0 0xbf0ff80ffe03fe3d 0xf2fc3fe03ff80ff8

def z835 : W := mkw 0xad07b8476e11ec9c 0x42b41ee11db847b2 0xbf2ff8cffe33ffff 0xfefcbfe33ff8cfff

def z836 : W := mkw 0x37f80001b5aa0020 0x00dfe00006d6a800 0x3ff80003ffff81f7 0xfcffe0000ffffe07

def z837 : W := mkw 0x3ffed6a800000000 0x08fffb5aa0000000 0xfffffffe0030001f 0xeffffffff800c000

def z838 : W := mkw 0x3daed6a800000000 0x08f6bb5aa0000000 0xf93ffffc0000000f 0xabe4fffff0000000

def z839 : W := mkw 0x0000001000040240 0x0000000040001009 0x013b18fe063f8fdf 0xbc04ec63f818fe3f

def z840 : W := mkw 0x37f8d229b5aa0020 0x08dfe348a6d6a800 0xbffbf8ffffff003f 0xfeffefe3fffffc00

def z841 : W := mkw 0x3ffed6a800000000 0x08fffb5aa0000000 0xfffffffe0633000f 0xebfffffff818cc00

def z842 : W := mkw 0x37f8d229b5aa0020 0x08dfe348a6d6a800 0xfffcff3fffff003f 0xfffff3fcfffffc00

def z843 : W := mkw 0x10a105c2c170d19b 0x044284170b05c346 0x78e007c3c1f0f1f2 0xede3801f0f07c3c7

def z844 : W := mkw 0x18a705c2c170d19b 0x04629c170b05c346 0xfee7e7c3c1f0f1ff 0xeffb9f9f0f07c3c7

def z845 : W := mkw 0xe758fa313e8e2e64 0x839d63e8c4fa38b9 0x8718f8303e0f0e09 0x121c63e0c0f83c38

def z846 : W := mkw 0x0806d6a800000000 0x08201b5aa0000000 0xf807fffc0000000c 0xebe01ffff0000000

def z847 : W := mkw 0xad07b8036e00ec1c 0x02b41ee00db803b0 0xbe04e003fe00fe3d 0x72f813800ff803f8

def z848 : W := mkw 0x2759d36ac170d19b 0x0c9d674dab05c346 0x8718f83fc1f0f1f9 0x061c63e0ff07c3c7

def z849 : W := mkw 0x880728036e00ec1c 0x02201ca00db803b0 0xbe07e003fe00fe3d 0xf2f81f800ff803f8

def z850 : W := mkw 0x080705c24050d19b 0x04201c1709014346 0x78c707c3c1c0f1f6 0xede31c1f0f0703c7

def z851 : W := mkw 0x08070142c170d19b 0x04201c050b05c346 0x78c70703c1f0f1f6 0xede31c1c0f07c3c7

def z852 : W := mkw 0x52f0433091ec1342 0x814bc10cc247b04d 0x40f0073001fc01c2 0x0d03c01cc007f007

def z853 : W := mkw 0x4258633018ce3b62 0x8109618cc06338ed 0xc6dce73039cfffff 0x7f1b739cc0e73fff

def z854 : W := mkw 0x18a705c2c170d19b 0x04629c170b05c346 0x78e307c3c1f0f1f2 0x8de38c1f0f07c3c7

def z855 : W := mkw 0x3ffed6a800000000 0x08fffb5aa0000000 0xfffffffc01c0003f 0xeffffffff0070000

def z856 : W := mkw 0x3ffed6a800000000 0x08fffb5aa0000000 0xff3ffffc0000000d 0x8bfcfffff0000000

def z857 : W := mkw 0x3ffed6a881200000 0x08fffb5aa2048000 0xfffffffdc1c0002f 0xebfffffff7070000

def z858 : W := mkw 0x4250633018cc3b42 0x8109418cc06330ed 0xc6d7fffc39ccffff 0x7f1b5ffff0e733ff

def z859 : W := mkw 0x37f8d6a800000000 0x08dfe35aa0000000 0xc7fbfffc0000000f 0xab1feffff0000000

def z860 : W := mkw 0x0806d6a9b5aa0020 0x08201b5aa6d6a800 0xc007ffffffff003c 0x1f001ffffffffc00

def z861 : W := mkw 0x3ffed6a800000000 0x08fffb5aa0000000 0xfffffffc003f000f 0xeffffffff000fc00

def z862 : W := mkw 0x3ffed6a9a5220020 0x08fffb5aa6948800 0xfffffffdc000000f 0xebfffffff7000000

def z863 : W := mkw 0x00000001b5aa0020 0x0000000006d6a800 0x38000003ffff0030 0xf4e000000ffffc00

def z864 : W := mkw 0x80012957ef75ffdf 0x460004a55fbdd7ff 0x00000003fffffff0 0x140000000fffffff

def z865 : W := mkw 0x2f56d22000000000 0x00bd5b4880000000 0xfffffffc0000000f 0xebfffffff0000000

def z866 : W := mkw 0x2750000134880000 0x009d400004d22000 0x3ff80003ffff0033 0xf4ffe0000ffffc00

def z867 : W := mkw 0x3ffed6a891aa0020 0x08fffb5aa246a800 0xfffffffc39ff003f 0xfffffffff0e7fc00

def z868 : W := mkw 0x37f80001b5aa0020 0x00dfe00006d6a800 0x3ff800ffffff0033 0xfcffe003fffffc00

def z869 : W := mkw 0x18a70dc2c370d59f 0x04629c370b0dc356 0x79ff1fffc7f0ffff 0xfde7fc7fff1fc3ff

def z870 : W := mkw 0x0250632008403902 0x0009418c802100e4 0xc6d4e73039c0ffff 0x7f1b539cc0e703ff

def z871 : W := mkw 0x0000200008002800 0x00000080002000a0 0xbe04e003f800fe3d 0xf2f813800fe003f8

def z872 : W := mkw 0x18a70102c160d11a 0x00629c040b058344 0x78e70703c1f0f1f6 0xede39c1c0f07c3c7

def z873 : W := mkw 0x18a705824040d11a 0x00629c1609010344 0x78e707c3c1c0f1f6 0xede39c1f0f0703c7

def z874 : W := mkw 0xad07bc8b6e00ec1c 0x0ab41ef22db803b0 0xbf07f8cffe00fe3d 0xf2fc1fe33ff803f8

def z875 : W := mkw 0x10a00001b5aa0020 0x0042800006d6a800 0x39f80003ffff0033 0xf4e7e0000ffffc00

def z876 : W := mkw 0x52f047f491fd13c3 0xc54bc11fd247f44f 0x40f807fc01ff01c2 0x0d03e01ff007fc07

def z877 : W := mkw 0x00010856021586d4 0x400004215808561b 0x393b18ffc63f8fff 0xfce4ec63ff18fe3f

def z878 : W := mkw 0x4250633018cc3b42 0x8109418cc06330ed 0xc7fce73039ccffff 0xff1ff39cc0e733ff

def z879 : W := mkw 0x18a70dc6c371d59f 0x44629c371b0dc756 0x78e71fcfc1f0f1f6 0xede39c7f3f07c3c7

def z880 : W := mkw 0x2f5ed6a800000000 0x08bd7b5aa0000000 0xc607fffc0000000c 0x0b181ffff0000000

def z881 : W := mkw 0xad07b8036e00ec1c 0x02b41ee00db803b0 0xbe04e001f800fe20 0x42f8138007e003f8

def z882 : W := mkw 0xe750fa353e8d2e44 0xc39d43e8d4fa34b9 0x8718f83c3e0f0e09 0x121c63e0f0f83c38

def z883 : W := mkw 0x18a60580c160510b 0x0462981603058144 0x78c40701c1c071e2 0x4de3101c070701c7

def z884 : W := mkw 0xad07b8036e00ec1c 0x02b41ee00db803b0 0xbf1ff83ffe00fe3d 0xf2fc7fe0fff803f8

def z885 : W := mkw 0x3ffed6a810880000 0x08fffb5aa0422000 0xfffffffc39c0002f 0xebfffffff0e70000

def z886 : W := mkw 0x0806d6a800000000 0x08201b5aa0000000 0xc607fffc0000000d 0x6b181ffff0000000

def z887 : W := mkw 0x250128032e00ac14 0x009404a00cb802b0 0xbf07f803fe00fe3d 0xf2fc1fe00ff803f8

def z888 : W := mkw 0x0806d6a800000000 0x08201b5aa0000000 0xc13ffffe063f001f 0xbf04fffff818fc00

def z889 : W := mkw 0xad0fb80b6e00ec1c 0x0ab43ee02db803b0 0xbf0ff80ffe00fe3d 0xf2fc3fe03ff803f8

def z890 : W := mkw 0xad07b8036e00ec1c 0x02b41ee00db803b0 0xbf04f803fe00fe39 0x52fc13e00ff803f8

def z891 : W := mkw 0x18a705c2c170d19b 0x04629c170b05c346 0x78e407c3c1f0f1f2 0x4de3901f0f07c3c7

def z892 : W := mkw 0xa500b8012e002c04 0x029402e004b800b0 0xbf04f803fe00fe3d 0xf2fc13e00ff803f8

def z893 : W := mkw 0xad07b8036e00ec1c 0x02b41ee00db803b0 0xbf03f803fe00fe39 0x92fc0fe00ff803f8

def z894 : W := mkw 0x37f89009b5aa0020 0x08dfe24026d6a800 0x3ff8180fffff0033 0xf4ffe0603ffffc00

def z895 : W := mkw 0x4250633018cc3b42 0x8109418cc06330ed 0xc6c4e73039c0fffd 0x7b1b139cc0e703ff

def z896 : W := mkw 0x0250210018c83902 0x00094084006320e4 0xc6d4e70039ccffff 0x7f1b539c00e733ff

def z897 : W := mkw 0xad06b0016c006808 0x02b41ac005b001a0 0xbf07f801f800fe3d 0xf2fc1fe007e003f8

def z898 : W := mkw 0x18a705c2c170d19b 0x04629c170b05c346 0x79e707c3c7f0f1f7 0xfde79c1f0f1fc3c7

def z899 : W := mkw 0x1afed6a800000000 0x086bfb5aa0000000 0xc0c7fffc0000000c 0x0b031ffff0000000

def z900 : W := mkw 0x35a80001b5aa0020 0x00d6a00006d6a800 0x39e80003ffff0032 0xf4e7a0000ffffc00

def z901 : W := mkw 0x675862313c8e2a60 0x819d6188c4f238a9 0x8610e030380c0e09 0x12184380c0e03038

def z902 : W := mkw 0xad07b8036e00ec1c 0x02b41ee00db803b0 0xffc7ff03fe00fe3f 0xfbff1ffc0ff803f8

def z903 : W := mkw 0x0806d6a800000000 0x08201b5aa0000000 0xc017fffc0000000f 0x2b005ffff0000000

def z904 : W := mkw 0xa50128036e00ec1c 0x029404a00db803b0 0xbf04e003fe00fe3d 0xf2fc13800ff803f8

def z905 : W := mkw 0x40012956dbfdffdf 0xc50004a55b6ff7ff 0x00000003fffffff0 0x140000000fffffff

def z906 : W := mkw 0xad0fb8036e02ec3c 0x02b43ee00db80bb0 0xbf0ff803fe03fe3d 0xf2fc3fe00ff80ff8

def z907 : W := mkw 0x3ffed6a924000000 0x08fffb5aa4900000 0xfffffffffe3f003f 0xfffffffffff8fc00

def z908 : W := mkw 0x37f80001b5aa0020 0x00dfe00006d6a800 0x3ffb1803ffff003f 0xf4ffec600ffffc00

def z909 : W := mkw 0x7ffef7a9bdea3922 0x89fffbdea6f7a8e4 0xfec4e701f9c07020 0x43fb139c07e701c0

def z910 : W := mkw 0x4250633018cc3b42 0x8109418cc06330ed 0xfed4e733f9ccffff 0xfffb539ccfe733ff

def z911 : W := mkw 0x1af6d6a800000000 0x086bdb5aa0000000 0xfef7fffc0000000f 0xebfbdffff0000000

def z912 : W := mkw 0x18a705c2c170d19b 0x04629c170b05c346 0x78e40703c1f0f1f2 0xe5e3901c0f07c3c7

def z913 : W := mkw 0x52f847b891ee1362 0x894be11ee247b84d 0x40f807fc01ff01c2 0x0d03e01ff007fc07

def z914 : W := mkw 0x3ffed6a881200000 0x08fffb5aa2048000 0xffffffffc7ff003f 0xffffffffff1ffc00

def z915 : W := mkw 0x10a0010081601102 0x0042800402058044 0x78c40701c1c0f1f6 0x6de3101c070703c7

def z916 : W := mkw 0x18a705c2c170d19b 0x04629c170b05c346 0x78e707c3c1f0ffff 0xfde39c1f0f07c3ff

def z917 : W := mkw 0x52f847f891fc13c3 0x8d4be11fe247f04f 0x40f807fc01fc01c2 0x0d03e01ff007f007

def z918 : W := mkw 0x00010856021586d4 0x400004215808561b 0x013b18fe063f8fcd 0x9804ec63f818fe3f

def z919 : W := mkw 0x37f80001b5aa0020 0x00dfe00006d6a800 0x3f380003ffff0031 0x94fce0000ffffc00

def z920 : W := mkw 0x0a56d6a800000000 0x08295b5aa0000000 0xc617fffc0000000d 0x0b185ffff0000000

def z921 : W := mkw 0x18a795cac170d19b 0x0c629e572b05c346 0x78e71fcfc1f0f1f6 0xede39c7f3f07c3c7

def z922 : W := mkw 0x37f80001b5aa0020 0x00dfe00006d6a800 0x3ffb00c3ffff0037 0xfcffec030ffffc00

def z923 : W := mkw 0x0250422000000000 0x0009410880000000 0xc6d7fffc0000000f 0x6b1b5ffff0000000

def z924 : W := mkw 0x37f80001b5aa0020 0x00dfe00006d6a800 0x7ffc0703ffff0037 0xfdfff01c0ffffc00

def z925 : W := mkw 0x4250633018cc3b42 0x8109418cc06330ed 0xc6d4e73039ccfff9 0x571b539cc0e733ff

def z926 : W := mkw 0x675062313c8c2a40 0x819d4188c4f230a9 0x8710e0303e0c0e09 0x121c4380c0f83038

def z927 : W := mkw 0x18a705c2c170d19b 0x04629c170b05c346 0x79e71fc3c1f0f1ff 0xede79c7f0f07c3c7

def z928 : W := mkw 0x10a1014281709192 0x004284050a05c246 0x78e707c3c1f0f1f6 0xede39c1f0f07c3c7

def z929 : W := mkw 0x18a70dc6c371d59f 0x44629c371b0dc756 0x79ff1fffc7f3f1ff 0xede7fc7fff1fcfc7

def z930 : W := mkw 0x37f80001b5aa0020 0x00dfe00006d6a800 0x3fc00003ffff0031 0xf4ff00000ffffc00

def z931 : W := mkw 0x12f846a800000000 0x084be11aa0000000 0xc7fffffc0000000f 0xeb1ffffff0000000

def z932 : W := mkw 0x18a6d6a800000000 0x08629b5aa0000000 0xf8c7fffc0000000c 0x4be31ffff0000000

def z933 : W := mkw 0x18af05cac170d19b 0x0c62bc172b05c346 0x78ef07cfc1f0f1f6 0xede3bc1f3f07c3c7

def z934 : W := mkw 0x4250633018cc3b42 0x8109418cc06330ed 0xc6f7e7f039ccffff 0xff1bdf9fc0e733ff

def z935 : W := mkw 0x2758d22800000000 0x089d6348a0000000 0xc7fffffc0000000f 0xeb1ffffff0000000

def z936 : W := mkw 0x37f8422000000000 0x00dfe10880000000 0xfffffffc0000000f 0xebfffffff0000000

def z937 : W := mkw 0x2d07b0024800e818 0x00b41ec0092003a0 0xbf07f803f800fe3d 0xf2fc1fe00fe003f8

def z938 : W := mkw 0x3daed6a800000000 0x08f6bb5aa0000000 0xf807fffc0000000c 0x0be01ffff0000000

def z939 : W := mkw 0x52f847f091fe13e3 0x854be11fc247f84f 0x40f807f001ff01c2 0x0d03e01fc007fc07

def z940 : W := mkw 0x37f8d6a9b5aa0020 0x08dfe35aa6d6a800 0xfff8ffffffff003b 0xffffe3fffffffc00

def z941 : W := mkw 0xad06b0016c006808 0x02b41ac005b001a0 0xbe04e001f800fe2c 0x42f8138007e003f8

def z942 : W := mkw 0xbffed6a964004008 0x0afffb5aa5900100 0xfffffffdc000000f 0xebfffffff7000000

def z943 : W := mkw 0x0a56d6a800000000 0x08295b5aa0000000 0xc6c7fffc0000000c 0x4b1b1ffff0000000

def z944 : W := mkw 0xad07b8036e00ec1c 0x02b41ee00db803b0 0xbe07f803f800fe3c 0xe2f81fe00fe003f8

def z945 : W := mkw 0x080601004040510a 0x0020180401010144 0x78c40701c1c0f1f6 0x6de3101c070703c7

def z946 : W := mkw 0x000108564215c6dc 0x400004215908571b 0x013b18ffc63fffff 0xbc04ec63ff18ffff

def z947 : W := mkw 0xad07b8036e00ec1c 0x02b41ee00db803b0 0xbf04e003fe00fe31 0xf2fc13800ff803f8

def z948 : W := mkw 0x52f8433091ee1362 0x814be10cc247b84d 0x40d0073001cc01c2 0x0d03401cc0073007

def z949 : W := mkw 0x3ffed6a891a80000 0x08fffb5aa246a000 0xfffffffff9fc003f 0xffffffffffe7f000

def z950 : W := mkw 0x37f846a9b5aa0020 0x08dfe11aa6d6a800 0xfffce7ffffff003f 0xfffff39ffffffc00

def z951 : W := mkw 0x37f80001b5aa0020 0x00dfe00006d6a800 0x3ff8183fffff003b 0xf4ffe060fffffc00

def z952 : W := mkw 0x18a60580c160510b 0x0462981603058144 0x78e40703c1f0f1f6 0xede3901c0f07c3c7

def z953 : W := mkw 0x18a605c0c170518b 0x046298170305c146 0x78e407c3c1f071f2 0xede3901f0f07c1c7

def z954 : W := mkw 0x10a10142c170d19b 0x044284050b05c346 0x78e40703c1f0f1f6 0xede3901c0f07c3c7

def z955 : W := mkw 0x18a605c0c170518b 0x046298170305c146 0x78c407c1c1c071e0 0x49e3101f070701c7

def z956 : W := mkw 0x6758f2393c8e2a60 0x899d63c8e4f238a9 0x8718f83c3e0f0e09 0x121c63e0f0f83c38

def z957 : W := mkw 0x18a6058081601102 0x0062981602058044 0x78e707c3c1f0f1f6 0xede39c1f0f07c3c7

def z958 : W := mkw 0x18a60580c160510b 0x0462981603058144 0x78e707c1c1c0f1f6 0xede39c1f070703c7

def z959 : W := mkw 0x080701424050d19a 0x00201c0509014346 0x78e707c3c1f0f1f6 0xede39c1f0f07c3c7

def z960 : W := mkw 0x2d06d6a800000000 0x08b41b5aa0000000 0xc707fffc0000000d 0x0b1c1ffff0000000

def z961 : W := mkw 0xad07b8036e00ec1c 0x02b41ee00db803b0 0xbf1ff803fe0ffe3d 0xf2fc7fe00ff83ff8

def z962 : W := mkw 0x4250633018cc3b42 0x8109418cc06330ed 0xc7d4e7323fccffff 0xff1f539cc8ff33ff

def z963 : W := mkw 0x4250633018cc3b42 0x8109418cc06330ed 0xc6d4e73039ccffee 0x4f1b539cc0e733ff

def z964 : W := mkw 0x400129560a55bfd6 0xc10004a5582956ff 0x000000000000ffc0 0x00000000000003ff

def z965 : W := mkw 0x00010856021586d4 0x400004215808561b 0x013b18fc063f8fcf 0x1c04ec63f018fe3f

def z966 : W := mkw 0xad07b8436e10ec9c 0x02b41ee10db843b2 0xbf3ff8c3fe3fffff 0xfefcffe30ff8ffff

def z967 : W := mkw 0xad07b8036e00ec1c 0x02b41ee00db803b0 0xbe07f803fe00fe3c 0x52f81fe00ff803f8

def z968 : W := mkw 0x3ffed6a924020020 0x08fffb5aa4900800 0xfffffffc0603000f 0xebfffffff0180c00

def z969 : W := mkw 0xad07b8036e00ec1c 0x02b41ee00db803b0 0xbf07f803fe00fe0d 0x92fc1fe00ff803f8

def z970 : W := mkw 0x37f84229b5aa0020 0x08dfe108a6d6a800 0x3ff8003fffff0033 0xf4ffe000fffffc00

def z971 : W := mkw 0x0a56d6a800000000 0x08295b5aa0000000 0xc0d7fffc0000000e 0x0b035ffff0000000

def z972 : W := mkw 0x4250633018cc3b42 0x8109418cc06330ed 0xc6fce73039ffffff 0x7f1bf39cc0e7ffff

def z973 : W := mkw 0x3ffed6a800000000 0x08fffb5aa0000000 0xfffffffc00000002 0xcbfffffff0000000

def z974 : W := mkw 0x3ffed6a934880000 0x08fffb5aa4d22000 0xffffffffffcc003f 0xffffffffffff3000

def z975 : W := mkw 0xad07b0036c00e818 0x02b41ec00db003a0 0xbe07e003f800fe3d 0xf2f81f800fe003f8

def z976 : W := mkw 0x12f80001b5aa0020 0x004be00006d6a800 0x38f80003ffff0032 0xf4e3e0000ffffc00

def z977 : W := mkw 0x4250633418cd3b42 0xc109418cd06334ed 0xc6dce73c39cfffff 0x7f1b739cf0e73fff

def z978 : W := mkw 0x18a705c2c170d19b 0x04629c170b05c346 0x79ff07c3c1f0f1f7 0xede7fc1f0f07c3c7

def z979 : W := mkw 0x3ffed6a8108a0020 0x08fffb5aa0422800 0xfffffffc000f000f 0xebfffffff0003c00

def z980 : W := mkw 0xc00129577eddffde 0xc30004a55dfb77ff 0x00000003fffffff0 0x140000000fffffff

def z981 : W := mkw 0x4250633018cc3b42 0x8109418cc06330ed 0xc7fffffe3fffffff 0xff1ffffff8ffffff

def z982 : W := mkw 0xad07b8436e10ec9c 0x02b41ee10db843b2 0xbf07f8c3fe00fffd 0xfafc1fe30ff803ff

def z983 : W := mkw 0xa501b8036e00ec1c 0x029406e00db803b0 0xbf00f803fe00fe39 0xf2fc03e00ff803f8

def z984 : W := mkw 0x37f80001b5aa0020 0x00dfe00006d6a800 0x3ef80003ffff0032 0x54fbe0000ffffc00

def z985 : W := mkw 0xad06b8016e006c0c 0x02b41ae005b801b0 0xbf07f801fe007e2d 0xf2fc1fe007f801f8

def z986 : W := mkw 0x18a705c2c170d19b 0x04629c170b05c346 0x78f707c3c1fcf1f7 0xfde3dc1f0f07f3c7

def z987 : W := mkw 0x4250633018cc3b42 0x8109418cc06330ed 0xc6d4e73039ccfff2 0x5f1b539cc0e733ff

def z988 : W := mkw 0x18a70dc2c370d59f 0x04629c370b0dc356 0x79ff1fc3c7ffffff 0xfde7fc7f0f1fffff

def z989 : W := mkw 0x3ffed6a9348a0020 0x08fffb5aa4d22800 0xfffffffc3800000f 0xebfffffff0e00000

def z990 : W := mkw 0x4250633018cc3b42 0x8109418cc06330ed 0xc7d7ff3039ccffff 0xff1f5ffcc0e733ff

def z991 : W := mkw 0x2d0720036c00e818 0x00b41c800db003a0 0xbf07e003fe00fe3d 0xf2fc1f800ff803f8

def z992 : W := mkw 0x3ffed6a881200000 0x08fffb5aa2048000 0xfffffffc01f0000f 0xeffffffff007c000

def z993 : W := mkw 0x37f84221b5aa0020 0x00dfe10886d6a800 0x7ff80733ffff0033 0xfdffe01ccffffc00

def z994 : W := mkw 0xad06b0016c006808 0x02b41ac005b001a0 0xbe04e001f800fe30 0x52f8138007e003f8

def z995 : W := mkw 0x18a705c2c170d19b 0x04629c170b05c346 0x78c70703c1f0f1f4 0xe5e31c1c0f07c3c7

def z996 : W := mkw 0x18a705c2c170d19b 0x04629c170b05c346 0x78e707c3c1f071e2 0xcde39c1f0f07c1c7

def z997 : W := mkw 0xad07bcc36e10ec9d 0x06b41ef30db843b2 0xbf07f8c3fe00fe3d 0xf2fc1fe30ff803f8

def z998 : W := mkw 0x12f0000091a80000 0x004bc0000246a000 0x3ff80003ffff0033 0xf4ffe0000ffffc00

def z999 : W := mkw 0x37f80489b5aa0020 0x08dfe01226d6a800 0x3ff800cfffff0033 0xf4ffe0033ffffc00

def z1000 : W := mkw 0xad07b8036e00ec1c 0x02b41ee00db803b0 0xbf27f8c3fe00fe3f 0xfafc9fe30ff803f8

def z1001 : W := mkw 0x18a70dc6c371d59f 0x44629c371b0dc756 0x78e707c3c7f3f1f6 0xede39c1f0f1fcfc7

def z1002 : W := mkw 0x25000001b5aa0020 0x0094000006d6a800 0x3f380003ffff0033 0xf4fce0000ffffc00

def z1003 : W := mkw 0xad07b8036e00ec1c 0x02b41ee00db803b0 0xbfc7f803ffc0fe3f 0xf6ff1fe00fff03f8

def z1004 : W := mkw 0x4000633008443b42 0x8100018cc02110ed 0xc6c4e73039c0ffff 0x7f1b139cc0e703ff

def z1005 : W := mkw 0x18a705c2c170d19b 0x04629c170b05c346 0x79ef1fcfc1f0f1f6 0xede7bc7f3f07c3c7

def z1006 : W := mkw 0x00000854021506c4 0x400000215008541b 0x013b18fc063f0fcf 0xbc04ec63f018fc3f

def z1007 : W := mkw 0x0806d6a800000000 0x08201b5aa0000000 0xc11ffffc0000000d 0x0b047ffff0000000

def z1008 : W := mkw 0x1afed6a800000000 0x086bfb5aa0000000 0xf8fffffc0000000e 0xebe3fffff0000000

def z1009 : W := mkw 0xad07b8036e00ec1c 0x02b41ee00db803b0 0xbf07f803fe00fe2c 0xc2fc1fe00ff803f8

def z1010 : W := mkw 0xc807fb764a55ffde 0xc3201fedd92957ff 0xc007fffc0000ffcc 0x0b001ffff00003ff

def z1011 : W := mkw 0xe750f2313c8c2a40 0x839d43c8c4f230a9 0x8610e030380c0e09 0x12184380c0e03038

def z1012 : W := mkw 0xad06b8016e006c0c 0x02b41ae005b801b0 0xbe04f801f8007e28 0x42f813e007e001f8

def z1013 : W := mkw 0x4250633018cc3b42 0x8109418cc06330ed 0xc6c4e70039c0ffe0 0x431b139c00e703ff

def z1014 : W := mkw 0x10a00001b5aa0020 0x0042800006d6a800 0x38c00003ffff0030 0x54e300000ffffc00

def z1015 : W := mkw 0xad07b8036e00ec1c 0x02b41ee00db803b0 0xbe07f801f800fe3d 0x72f81fe007e003f8

def z1016 : W := mkw 0x37f80001b5aa0020 0x00dfe00006d6a800 0x39f80003ffff0032 0x94e7e0000ffffc00

def z1017 : W := mkw 0x48076ff64a55ffdf 0xc5201dbfd92957ff 0xc007fffc0000ffcc 0x0b001ffff00003ff

def z1018 : W := mkw 0x67586a353e8f2e64 0xc19d61a8d4fa3cb9 0x8718f83c3e0f0e09 0x121c63e0f0f83c38

def z1019 : W := mkw 0x3ffed6a9348a0020 0x08fffb5aa4d22800 0xfffffffffe0f003f 0xfbfffffffff83c00

def z1020 : W := mkw 0x35a00001a5200000 0x00d6800006948000 0x3ff80003ffff0033 0xf4ffe0000ffffc00

def z1021 : W := mkw 0x4000211018cc3b42 0x81000084406330ed 0xc6c4e70039ccffff 0x7f1b139c00e733ff

def z1022 : W := mkw 0x3ffed6a800000000 0x08fffb5aa0000000 0xfffbfffc0000000b 0x8bffeffff0000000

def z1023 : W := mkw 0xad07b8036e00ec1c 0x02b41ee00db803b0 0xbe07e003fe00fe34 0xf2f81f800ff803f8

def z1024 : W := mkw 0x0806d6a800000000 0x08201b5aa0000000 0xc0c7fffc0000000e 0x6b031ffff0000000

def z1025 : W := mkw 0x18af05c2c172d1bb 0x0462bc170b05cb46 0x78ef07c3c1f3f1f6 0xede3bc1f0f07cfc7

def z1026 : W := mkw 0x400129560a55bfd6 0xc10004a5582956ff 0x00000002063fffd0 0x140000000818ffff

def z1027 : W := mkw 0x4250633018cc3b42 0x8109418cc06330ed 0xc6d4e73039ccffed 0x5b1b539cc0e733ff

def z1028 : W := mkw 0x3ffed6a9a5220020 0x08fffb5aa6948800 0xffffffffc63f001f 0xffffffffff18fc00

def z1029 : W := mkw 0x37f80481b5aa0020 0x00dfe01206d6a800 0x7ff807c3ffff0033 0xfdffe01f0ffffc00

def z1030 : W := mkw 0x0806d6a800000000 0x08201b5aa0000000 0xc107fffc0000000d 0xab041ffff0000000

def z1031 : W := mkw 0x00010856021586d4 0x400004215808561b 0x073b18fe3e3f8fff 0xfc1cec63f8f8fe3f

def z1032 : W := mkw 0x0000010000401102 0x0000000400010044 0x78c40703c1c0f1f6 0xede3101c0f0703c7

def z1033 : W := mkw 0x37f80001b5aa0020 0x00dfe00006d6a800 0x3ed00003ffff0033 0x74fb40000ffffc00

def z1034 : W := mkw 0x2f5ed6a800000000 0x08bd7b5aa0000000 0xc7dffffc0000000f 0x6b1f7ffff0000000

def z1035 : W := mkw 0xad06b0016c006808 0x02b41ac005b001a0 0xbe04e001f8007e29 0x52f8138007e001f8

def z1036 : W := mkw 0x18a60580c160510b 0x0462981603058144 0x78c40701c1c0f1f0 0x45e3101c070703c7

def z1037 : W := mkw 0x3ffed6a800000000 0x08fffb5aa0000000 0xffc7fffc0000000d 0xebff1ffff0000000

def z1038 : W := mkw 0x18a70dc2c370d59f 0x04629c370b0dc356 0x78e707c3c7f0fff6 0xfde39c1f0f1fc3ff

def z1039 : W := mkw 0x00010856021586d4 0x400004215808561b 0x01fb18fe07ff8fff 0xfc07ec63f81ffe3f

def z1040 : W := mkw 0x98a79dc2c370d59f 0x06629e770b0dc356 0x78e71fc3c1f0f1f6 0xede39c7f0f07c3c7

def z1041 : W := mkw 0x18a605c0c170518b 0x046298170305c146 0x78e407c1c1f0f1f6 0x6de3901f0707c3c7

def z1042 : W := mkw 0x35a80001b5aa0020 0x00d6a00006d6a800 0x39380003ffff0033 0xb4e4e0000ffffc00

def z1043 : W := mkw 0x18a6d6a800000000 0x08629b5aa0000000 0xf827fffc0000000c 0x8be09ffff0000000

def z1044 : W := mkw 0x250020012c002800 0x0094008004b000a0 0xbe04e001f800fe3d 0x72f8138007e003f8

def z1045 : W := mkw 0x3ffed6a9a5200000 0x08fffb5aa6948000 0xfffffffffff0003f 0xffffffffffffc000

def z1046 : W := mkw 0x18a705c2c170d19b 0x04629c170b05c346 0x7ee707c3f9f0f1f7 0xfdfb9c1f0fe7c3c7

def z1047 : W := mkw 0x35a80001b5aa0020 0x00d6a00006d6a800 0x38000003ffff0030 0x14e000000ffffc00

def z1048 : W := mkw 0x18a70dc2c370d59f 0x04629c370b0dc356 0x79e71fc3c7f0f1f6 0xede79c7f0f1fc3c7

def z1049 : W := mkw 0x2d0ed6a800000000 0x08b43b5aa0000000 0xc10ffffc0000000c 0x0b043ffff0000000

def z1050 : W := mkw 0x3ffed6a924000000 0x08fffb5aa4900000 0xffffffffc600000f 0xebffffffff180000

def z1051 : W := mkw 0x3ffed6a881220020 0x08fffb5aa2048800 0xfffffffc0033000f 0xebfffffff000cc00

def z1052 : W := mkw 0x37f89001b5aa0020 0x00dfe24006d6a800 0xbff8f803ffff003b 0xf6ffe3e00ffffc00

def z1053 : W := mkw 0x3ffed6a800000000 0x08fffb5aa0000000 0xfffffffc0000f03f 0xebfffffff00003c0

def z1054 : W := mkw 0x4250633018cc3b42 0x8109418cc06330ed 0xc6d4e7323fffffff 0x7f1b539cc8ffffff

def z1055 : W := mkw 0x3ffed6a810880000 0x08fffb5aa0422000 0xfffffffe3fff003f 0xfffffffff8fffc00

def z1056 : W := mkw 0x8807b8024a00ec1c 0x02201ee0092803b0 0xbe07f803f800fe3d 0xf2f81fe00fe003f8

def z1057 : W := mkw 0x18a6d6a881200000 0x08629b5aa2048000 0xf8e7ffffc1f0003e 0xefe39fffff07c000

def z1058 : W := mkw 0x0250422010880000 0x0009410880422000 0xc7fffffe3fff003f 0xff1ffffff8fffc00

def z1059 : W := mkw 0x18a60580c160510b 0x0462981603058144 0x78c40701c1c0f1e4 0x49e3101c070703c7

def z1060 : W := mkw 0x37f80001b5aa0020 0x00dfe00006d6a800 0xbffce003ffff003f 0xf6fff3800ffffc00

def z1061 : W := mkw 0x52f8437491ff13e2 0xc14be10dd247fc4f 0x40f807fc01ff01c2 0x0d03e01ff007fc07

def z1062 : W := mkw 0x3ffed6a9b5aa0020 0x08fffb5aa6d6a800 0xfffffffffe3f000f 0xfbfffffffff8fc00

def z1063 : W := mkw 0x0000211008443b42 0x00000084402110ed 0xc6d4e73039ccffff 0x7f1b539cc0e733ff

def z1064 : W := mkw 0x18a705c6c171d19b 0x44629c171b05c746 0x78ef07cfc1f3f1f6 0xede3bc1f3f07cfc7

def z1065 : W := mkw 0x40012957bfffbff6 0xc10004a55efffeff 0x00000003fffffff0 0x140000000fffffff

def z1066 : W := mkw 0xad07b8036e00ec1c 0x02b41ee00db803b0 0xbf07f803fe00fe30 0xd2fc1fe00ff803f8

def z1067 : W := mkw 0x2d06d6a800000000 0x08b41b5aa0000000 0xff3ffffc0000000f 0xebfcfffff0000000

def z1068 : W := mkw 0x18a705c2c170d19b 0x04629c170b05c346 0x78e707c3c1f0f1e4 0xc9e39c1f0f07c3c7

def z1069 : W := mkw 0x37f80001b5aa0020 0x00dfe00006d6a800 0x3ff80033ffff003f 0xfcffe000cffffc00

def z1070 : W := mkw 0x18a70dc2c370d59f 0x04629c370b0dc356 0x78e71fc3c1f0fffe 0xede39c7f0f07c3ff

def z1071 : W := mkw 0x3ffed6a9b5aa0020 0x08fffb5aa6d6a800 0xfffffffdf9cc003f 0xfffffffff7e73000

def z1072 : W := mkw 0xad07bc836e00ec1c 0x02b41ef20db803b0 0xff07ffc3fe00fe3d 0xfbfc1fff0ff803f8

def z1073 : W := mkw 0x3daed6a800000000 0x08f6bb5aa0000000 0xf9effffc0000000e 0xebe7bffff0000000

def z1074 : W := mkw 0x00010856021586d4 0x400004215808561b 0x013b18fe063f8fd9 0x9404ec63f818fe3f

def z1075 : W := mkw 0x00010856021586d4 0x400004215808561b 0x013b18fe063f8fd2 0x9c04ec63f818fe3f

def z1076 : W := mkw 0x3ffed6a9b5aa0020 0x08fffb5aa6d6a800 0xfffffffdffcf002f 0xfbfffffff7ff3c00

def z1077 : W := mkw 0x4250633018cc3b42 0x8109418cc06330ed 0xc6d4e70039ccfff3 0x771b539c00e733ff

def z1078 : W := mkw 0x00010856021586d4 0x400004215808561b 0x873ff8fe063f8fdf 0xfe1cffe3f818fe3f

def z1079 : W := mkw 0xad07b8036e00ec1c 0x02b41ee00db803b0 0xbf07f801fe00fe2d 0x52fc1fe007f803f8

def z1080 : W := mkw 0x18a705c2c170d19b 0x04629c170b05c346 0x78e707c1c1f0f1e6 0x4de39c1f0707c3c7

def z1081 : W := mkw 0x12f00001b5aa0020 0x004bc00006d6a800 0x3ef00003ffff0033 0xf4fbc0000ffffc00

def z1082 : W := mkw 0xad07b8436e10ec9c 0x02b41ee10db843b2 0xbf27f8c3fe30fe3d 0xf2fc9fe30ff8c3f8

def z1083 : W := mkw 0xad07b8036e00ec1c 0x02b41ee00db803b0 0xbf07f803fe3ffe3d 0xf6fc1fe00ff8fff8

def z1084 : W := mkw 0x3ffed6a800000000 0x08fffb5aa0000000 0xffeffffc0000000c 0xcbffbffff0000000

def z1085 : W := mkw 0x18a6d6a800000000 0x08629b5aa0000000 0xf9fffffc0000000f 0xebe7fffff0000000

def z1086 : W := mkw 0x37f84221b5aa0020 0x00dfe10886d6a800 0xfffce703ffff0033 0xf7fff39c0ffffc00

def z1087 : W := mkw 0x425129561addbfd6 0xc10944a5586b76ff 0x07f800023ffffff3 0xf41fe00008ffffff

def z1088 : W := mkw 0x4250633018cc3b42 0x8109418cc06330ed 0xc6d4e73039c0ffef 0x6b1b539cc0e703ff

def z1089 : W := mkw 0xad06b8016e006c0c 0x02b41ae005b801b0 0xbe04e001fe007e20 0x52f8138007f801f8

def z1090 : W := mkw 0x37f80001b5aa0020 0x00dfe00006d6a800 0x3fd80003ffff0031 0x54ff60000ffffc00

def z1091 : W := mkw 0x18a705c2c170d19b 0x04629c170b05c346 0x78e707c1c1c0f1e6 0xe9e39c1f070703c7

def z1092 : W := mkw 0xad07b8036e00ec1c 0x02b41ee00db803b0 0xbf17f803fe0cfe3f 0xf6fc5fe00ff833f8

def z1093 : W := mkw 0x3ffed6a800000000 0x08fffb5aa0000000 0xfffffffc00008e1f 0xfbfffffff0000238

def z1094 : W := mkw 0x0a56d6a800000000 0x08295b5aa0000000 0xc7fffffc0000000f 0xeb1ffffff0000000

def z1095 : W := mkw 0x3ffed6a800000000 0x08fffb5aa0000000 0xffffffffc000003f 0xebffffffff000000

def z1096 : W := mkw 0x3ffed6a8c1204009 0x0cfffb5aa3048100 0xfffffffdc000000f 0xebfffffff7000000

def z1097 : W := mkw 0x3ffed6a9a5220020 0x08fffb5aa6948800 0xfffffffffe33003f 0xfbfffffffff8cc00

def z1098 : W := mkw 0xad07b8436e10ec9c 0x02b41ee10db843b2 0xbf07f803fe30fffd 0xf6fc1fe00ff8c3ff

def z1099 : W := mkw 0x18a705c2c170d19b 0x04629c170b05c346 0x78ff07ffc1f0f1f6 0xede3fc1fff07c3c7

def z1100 : W := mkw 0xad07b8036e00ec1c 0x02b41ee00db803b0 0xbf07f803fe007e29 0xd2fc1fe00ff801f8

def z1101 : W := mkw 0x3ffed6a800000000 0x08fffb5aa0000000 0xfee7fffc0000000e 0xebfb9ffff0000000

def z1102 : W := mkw 0x0806d6a800000000 0x08201b5aa0000000 0xc03ffffc0000000e 0x0b00fffff0000000

def z1103 : W := mkw 0x00010856021586d4 0x400004215808561b 0x013f18fe063fffff 0xfc04fc63f818ffff

def z1104 : W := mkw 0x0000422000000000 0x0000010880000000 0xc13ffffc0000000f 0xab04fffff0000000

def z1105 : W := mkw 0x3ffed6a800000000 0x08fffb5aa0000000 0xfffffffc00000009 0xc3fffffff0000000

def z1106 : W := mkw 0x4250633018cc3b42 0x8109418cc06330ed 0xc6d4e73039ccffcf 0x1f1b539cc0e733ff

def z1107 : W := mkw 0x0a5ed6a800000000 0x08297b5aa0000000 0xc01ffffc0000000c 0x0b007ffff0000000

def z1108 : W := mkw 0x3ffed6a891aa0020 0x08fffb5aa246a800 0xfffffffc01c0000f 0xebfffffff0070000

def z1109 : W := mkw 0x1af646a000000000 0x006bd91a80000000 0xfffffffc0000000f 0xebfffffff0000000

def z1110 : W := mkw 0x3daed6a9a5220020 0x08f6bb5aa6948800 0xf92fffffc633000c 0x8be4bfffff18cc00

def z1111 : W := mkw 0xad07b8476e11ec9c 0x42b41ee11db847b2 0xbf07f8cffe00fe3d 0xf2fc1fe33ff803f8

def z1112 : W := mkw 0x25000001b5aa0020 0x0094000006d6a800 0x3e000003ffff0030 0x54f800000ffffc00

def z1113 : W := mkw 0x4250633018cc3b42 0x8109418cc06330ed 0xc6c4e73039c0fffe 0x6f1b139cc0e703ff

def z1114 : W := mkw 0x18a6d6a800000000 0x08629b5aa0000000 0xc0e7fffc0000000e 0x0b039ffff0000000

def z1115 : W := mkw 0x10a00001b5aa0020 0x0042800006d6a800 0x38200003ffff0030 0x94e080000ffffc00

def z1116 : W := mkw 0x3ffed6a800000000 0x08fffb5aa0000000 0xfffffffe0600001f 0xfbfffffff8180000

def z1117 : W := mkw 0xad07b8036e00ec1c 0x02b41ee00db803b0 0xbf17f833fe00fe3f 0xfafc5fe0cff803f8

def z1118 : W := mkw 0xad07b8036e00ec1c 0x02b41ee00db803b0 0xbf07f803fe00ffff 0xfefc1fe00ff803ff

def z1119 : W := mkw 0x37f80001b5aa0020 0x00dfe00006d6a800 0x3ee00003ffff0032 0xf4fb80000ffffc00

def z1120 : W := mkw 0xad06b0016c006808 0x02b41ac005b001a0 0xbf04e003fe00fe3d 0xf2fc13800ff803f8

def z1121 : W := mkw 0x10a005c081701183 0x044280170205c046 0x78e407c3c1f0f1f6 0xede3901f0f07c3c7

def z1122 : W := mkw 0x00010856021586d4 0x400004215808561b 0x013b18fe063f8fce 0x8c04ec63f818fe3f

def z1123 : W := mkw 0x080728024a00ec1c 0x00201ca0092803b0 0xbf07f803fe00fe3d 0xf2fc1fe00ff803f8

def z1124 : W := mkw 0x0806d6a800000000 0x08201b5aa0000000 0xc027fffc0000000e 0xab009ffff0000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z7,z1,z3,z4,z5,z6]),(0,[z8,z0,z1,z3,z9,z5,z6]),(0,[z0,z1,z3,z4,z5,z10,z6]),(1,[z0,z11,z12,z4,z5,z6]),(0,[z0,z1,z13,z4,z9,z5,z6]),(0,[z0,z1,z3,z14,z4,z5,z6])],[(0,[z15,z0,z1,z3,z4,z5,z16]),(1,[z0,z1,z3,z4,z5,z17]),(0,[z0,z1,z18,z3,z4,z5,z6]),(0,[z0,z1,z3,z9,z19,z5,z6]),(0,[z0,z20,z1,z3,z21,z5,z6]),(0,[z0,z1,z3,z4,z21,z22,z6]),(0,[z0,z23,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z24,z6]),(0,[z0,z25,z1,z3,z4,z5,z6]),(0,[z0,z1,z13,z4,z26,z5,z6]),(0,[z0,z1,z3,z4,z27,z5,z6]),(0,[z0,z1,z28,z3,z4,z5,z6])],[(0,[z0,z29,z1,z3,z4,z5,z6]),(0,[z0,z30,z3,z4,z31,z5,z6])],[(1,[z0,z32,z4,z33,z5,z6]),(0,[z34,z0,z1,z3,z4,z5,z6]),(0,[z0,z20,z1,z3,z35,z5,z6]),(0,[z0,z1,z3,z4,z36,z5,z6])],[(0,[z0,z1,z3,z4,z37,z5,z6]),(0,[z0,z1,z3,z4,z38,z5,z6]),(0,[z0,z1,z3,z4,z39,z5,z6]),(0,[z0,z40,z1,z3,z41,z5,z6])],[(0,[z42,z0,z1,z3,z4,z5,z6]),(0,[z0,z43,z1,z3,z4,z5,z6]),(0,[z44,z1,z3,z4,z5,z45,z6]),(0,[z0,z1,z3,z36,z9,z5,z6]),(0,[z0,z20,z1,z3,z5,z46,z6]),(0,[z0,z1,z3,z47,z4,z5,z6]),(0,[z0,z1,z3,z48,z4,z5,z6])],[(1,[z15,z49,z3,z4,z5,z6]),(0,[z0,z50,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z51,z4,z52,z6]),(0,[z0,z1,z3,z4,z5,z53,z6])],[(0,[z54,z0,z1,z3,z4,z5,z6]),(0,[z0,z55,z20,z1,z3,z5,z6]),(0,[z56,z0,z20,z1,z3,z5,z6]),(0,[z0,z1,z57,z3,z4,z5,z6])]],
   [[(0,[z58,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z59,z6]),(0,[z0,z60,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z61,z6])],[(0,[z0,z1,z62,z4,z9,z5,z6]),(0,[z0,z1,z3,z4,z5,z63,z6]),(0,[z0,z20,z1,z64,z3,z5,z6]),(0,[z0,z1,z65,z3,z4,z5,z6]),(0,[z0,z66,z1,z3,z4,z5,z6])],[(0,[z67,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z68,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z69])],[(1,[z0,z1,z3,z70,z5,z6]),(0,[z0,z71,z1,z3,z4,z5,z6]),(0,[z72,z0,z1,z3,z52,z5,z6]),(0,[z73,z0,z1,z3,z4,z5,z6]),(0,[z74,z0,z1,z3,z4,z5,z75]),(0,[z76,z0,z77,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z78,z6]),(0,[z0,z1,z3,z4,z5,z79,z6]),(0,[z0,z1,z4,z5,z80,z6,z81]),(0,[z0,z1,z3,z4,z82,z5,z6])],[(1,[z0,z83,z3,z4,z5,z6]),(0,[z0,z84,z1,z3,z4,z5,z6]),(0,[z0,z1,z85,z3,z4,z5,z6]),(1,[z0,z32,z1,z9,z5,z6]),(0,[z0,z1,z3,z4,z86,z5,z6]),(0,[z0,z1,z87,z3,z9,z5,z6]),(1,[z0,z88,z1,z3,z5,z6])],[(0,[z0,z1,z3,z4,z5,z89,z6]),(0,[z44,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z90,z6]),(0,[z8,z0,z91,z3,z4,z5,z6]),(0,[z0,z92,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z93,z46])],[(0,[z0,z94,z3,z4,z33,z5,z6]),(0,[z0,z20,z1,z3,z5,z6,z75]),(0,[z0,z1,z3,z95,z4,z5,z6]),(0,[z0,z1,z3,z96,z4,z5,z6]),(0,[z0,z97,z1,z3,z4,z5,z6]),(1,[z0,z98,z1,z3,z5,z99])],[(0,[z100,z0,z1,z3,z4,z5,z6]),(0,[z0,z101,z3,z4,z5,z6,z102])]],
   [[(1,[z0,z1,z103,z4,z5,z6]),(0,[z0,z104,z1,z3,z35,z5,z6])],[(0,[z0,z105,z1,z3,z4,z5,z6]),(0,[z0,z106,z94,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z107]),(0,[z108,z0,z1,z3,z4,z5,z6]),(0,[z0,z109,z1,z3,z47,z5,z6])],[(0,[z0,z1,z110,z3,z4,z5,z6]),(1,[z58,z1,z62,z4,z5,z6]),(0,[z0,z1,z3,z4,z52,z21,z6]),(0,[z0,z1,z3,z4,z5,z6,z111])],[(0,[z0,z112,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z113,z6]),(0,[z0,z1,z3,z4,z5,z114,z6]),(1,[z0,z1,z3,z47,z5,z6])],[(0,[z0,z115,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z26,z21,z6]),(0,[z0,z32,z1,z116,z3,z5,z6]),(0,[z117,z0,z1,z3,z4,z5,z6]),(0,[z118,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z9,z5,z80,z6]),(0,[z0,z20,z1,z3,z5,z6,z119]),(0,[z0,z1,z3,z4,z5,z6,z120]),(0,[z0,z1,z121,z3,z4,z5,z6]),(0,[z122,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z123,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z124,z6])],[(0,[z125,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z126,z6]),(0,[z0,z1,z3,z4,z5,z6,z127]),(0,[z0,z1,z3,z9,z128,z5,z6]),(0,[z0,z20,z129,z1,z3,z5,z6])],[(0,[z0,z1,z3,z130,z4,z5,z6])],[(0,[z0,z1,z49,z3,z9,z5,z6]),(0,[z0,z94,z3,z4,z35,z5,z6]),(0,[z131,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z132,z6]),(0,[z133,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z134])]],
   [[(0,[z135,z0,z136,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z75,z102]),(0,[z0,z1,z3,z4,z137,z5,z138]),(0,[z0,z1,z3,z4,z139,z5,z6]),(1,[z0,z20,z1,z9,z5,z6]),(0,[z0,z1,z140,z4,z5,z6,z81]),(0,[z0,z98,z1,z3,z5,z99,z6])],[(0,[z141,z0,z49,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z80,z138]),(0,[z0,z101,z1,z3,z4,z5,z142]),(0,[z0,z1,z3,z9,z143,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z144])],[(0,[z8,z0,z1,z3,z4,z5,z138]),(0,[z0,z1,z3,z4,z145,z5,z6]),(0,[z0,z11,z1,z4,z33,z5,z6]),(0,[z146,z0,z30,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z147,z6]),(0,[z0,z148,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z149,z6])],[(0,[z76,z0,z94,z3,z4,z5,z6]),(0,[z0,z150,z1,z3,z4,z5,z6]),(0,[z151,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z9,z5,z138,z6]),(0,[z0,z20,z104,z1,z3,z5,z6]),(0,[z0,z1,z3,z152,z4,z5,z6]),(0,[z0,z153,z1,z3,z51,z5,z6])],[(0,[z0,z1,z1,z3,z4,z5,z6]),(0,[z0,z20,z1,z3,z5,z45,z6]),(0,[z0,z1,z154,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z155,z5,z6]),(0,[z0,z156,z1,z3,z4,z5,z6])],[(0,[z157,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z158,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z159])],[(0,[z135,z0,z1,z3,z9,z5,z6]),(0,[z0,z1,z160,z3,z4,z5,z6]),(0,[z118,z0,z1,z140,z4,z5,z6]),(0,[z0,z20,z1,z13,z3,z5,z6])],[(0,[z15,z1,z49,z3,z4,z5,z6]),(0,[z0,z1,z3,z3,z4,z5,z6]),(0,[z161,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z140,z4,z9,z5,z6]),(0,[z0,z1,z140,z3,z155,z5,z6]),(0,[z0,z1,z3,z4,z41,z5,z6])]],
   [[(0,[z0,z1,z162,z3,z4,z5,z6]),(0,[z58,z0,z20,z1,z3,z5,z6]),(0,[z0,z32,z1,z4,z33,z5,z6]),(0,[z0,z163,z1,z3,z4,z5,z164])],[(0,[z0,z1,z165,z3,z4,z5,z6]),(0,[z166,z0,z1,z3,z4,z5,z75]),(0,[z0,z167,z1,z3,z4,z5,z6])],[(0,[z0,z11,z49,z3,z4,z5,z6]),(0,[z135,z0,z1,z3,z4,z5,z168]),(0,[z0,z1,z3,z4,z5,z6,z169]),(0,[z0,z77,z3,z4,z35,z5,z6]),(0,[z0,z170,z1,z3,z4,z5,z6]),(0,[z0,z171,z1,z3,z4,z5,z6])],[(0,[z58,z0,z1,z3,z4,z172,z6]),(1,[z0,z20,z1,z3,z5,z6]),(0,[z0,z1,z13,z3,z9,z5,z6])],[(0,[z0,z94,z1,z3,z9,z5,z6]),(0,[z0,z40,z1,z3,z9,z5,z6]),(0,[z0,z1,z173,z3,z4,z5,z46]),(0,[z0,z1,z3,z51,z4,z5,z6])],[(0,[z0,z1,z3,z174,z4,z5,z6]),(0,[z44,z0,z20,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z45,z22,z6]),(0,[z8,z0,z175,z3,z4,z5,z6]),(0,[z0,z32,z1,z3,z176,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z177]),(0,[z0,z1,z3,z4,z5,z6,z178]),(0,[z179,z0,z1,z3,z4,z5,z6])],[(0,[z15,z0,z94,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z21,z46,z6]),(0,[z146,z0,z32,z3,z4,z5,z6]),(0,[z0,z1,z3,z180,z4,z5,z6]),(0,[z0,z1,z3,z181,z4,z5,z6]),(0,[z0,z3,z4,z31,z5,z164,z6]),(0,[z0,z3,z4,z31,z5,z142,z6]),(0,[z0,z1,z3,z182,z4,z5,z6]),(0,[z0,z1,z3,z9,z5,z6,z183]),(0,[z0,z184,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z185,z5,z6]),(0,[z74,z0,z1,z3,z4,z5,z124]),(0,[z0,z1,z3,z4,z124,z6,z186])],[(0,[z0,z1,z3,z4,z143,z5,z6]),(0,[z0,z1,z187,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z188,z5,z6]),(0,[z0,z189,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z9,z31,z5,z6]),(0,[z0,z1,z3,z9,z137,z5,z6]),(0,[z0,z88,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z190,z4,z5,z6])]],
   [[(0,[z94,z1,z49,z3,z4,z5,z6]),(0,[z191,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z192,z4,z5,z6]),(0,[z193,z0,z1,z3,z4,z5,z6]),(0,[z0,z194,z1,z3,z4,z5,z6])],[(0,[z195,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z196,z3,z4,z5,z6]),(0,[z135,z0,z1,z3,z4,z21,z6]),(0,[z0,z1,z3,z4,z5,z138,z6]),(1,[z0,z1,z116,z3,z5,z6]),(0,[z0,z1,z116,z3,z4,z5,z6]),(0,[z0,z1,z3,z9,z5,z142,z6]),(0,[z108,z0,z20,z1,z3,z5,z6]),(0,[z0,z197,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z198,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z199,z6])],[(0,[z141,z15,z1,z3,z4,z5,z6]),(0,[z0,z200,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z201,z5,z6]),(0,[z0,z1,z3,z9,z5,z6,z81]),(0,[z0,z1,z3,z9,z5,z202,z6]),(0,[z0,z20,z1,z3,z5,z80,z6]),(0,[z0,z20,z1,z3,z51,z5,z6])],[(0,[z0,z1,z3,z4,z5,z203,z6]),(0,[z0,z1,z3,z4,z5,z204,z6]),(0,[z166,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z205,z6]),(1,[z0,z1,z3,z155,z5,z6])],[(0,[z0,z30,z1,z3,z9,z5,z6]),(0,[z118,z0,z20,z1,z3,z5,z6])],[(0,[z0,z1,z3,z4,z206,z5,z6]),(0,[z0,z1,z3,z4,z207,z5,z6]),(0,[z0,z1,z3,z4,z5,z208,z6])],[(0,[z0,z1,z3,z4,z5,z209,z6]),(0,[z0,z1,z3,z4,z210,z5,z6]),(0,[z166,z8,z1,z3,z4,z5,z6]),(0,[z211,z0,z1,z3,z4,z5,z6]),(0,[z0,z40,z1,z140,z4,z5,z6]),(1,[z0,z1,z3,z41,z5,z6]),(0,[z212,z0,z1,z3,z4,z5,z6])],[(0,[z0,z106,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z22,z6])]],
   [[(0,[z213,z0,z1,z3,z4,z5,z6]),(1,[z0,z175,z3,z4,z5,z6]),(0,[z214,z0,z1,z3,z4,z5,z6]),(0,[z0,z215,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z9,z52,z5,z6])],[(0,[z0,z49,z3,z4,z5,z6,z102]),(0,[z161,z0,z1,z3,z4,z216,z6]),(0,[z0,z217,z1,z3,z4,z5,z6]),(0,[z0,z1,z77,z3,z9,z5,z6]),(0,[z0,z101,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z218,z6]),(0,[z56,z0,z1,z3,z9,z5,z6]),(0,[z0,z1,z3,z9,z26,z5,z6]),(0,[z0,z219,z1,z3,z4,z5,z6])],[(0,[z220,z0,z1,z3,z4,z5,z6]),(0,[z221,z0,z1,z3,z4,z5,z6]),(0,[z0,z11,z1,z3,z9,z5,z6]),(0,[z0,z3,z4,z5,z142,z6,z102]),(0,[z222,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z223,z3,z9,z5,z6]),(0,[z0,z1,z3,z4,z5,z224,z6]),(0,[z0,z1,z3,z225,z4,z5,z6]),(0,[z226,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z227,z5,z6]),(0,[z0,z1,z3,z228,z4,z5,z6]),(0,[z0,z1,z3,z4,z229,z5,z6]),(0,[z0,z98,z1,z87,z3,z5,z6])],[(0,[z0,z1,z3,z4,z31,z5,z6]),(0,[z0,z230,z1,z3,z4,z5,z6])],[(0,[z231,z0,z1,z3,z4,z5,z6]),(0,[z0,z232,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z233,z5,z6]),(0,[z0,z1,z3,z4,z234,z5,z6]),(0,[z0,z1,z3,z4,z235,z5,z6]),(0,[z0,z1,z236,z3,z4,z5,z6])],[(0,[z161,z0,z20,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z164,z6]),(0,[z0,z1,z3,z4,z5,z142,z6]),(0,[z0,z1,z3,z237,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z238])]],
   [[(0,[z0,z1,z3,z4,z239,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z81]),(0,[z0,z1,z3,z4,z5,z6,z240])],[(0,[z76,z0,z1,z3,z4,z5,z6]),(0,[z0,z20,z1,z3,z5,z6,z241]),(0,[z0,z242,z1,z3,z4,z5,z6])],[(0,[z0,z243,z1,z3,z4,z5,z6])],[(0,[z161,z0,z153,z1,z3,z5,z6]),(0,[z0,z1,z3,z9,z33,z5,z6]),(0,[z118,z0,z11,z1,z4,z5,z6]),(0,[z0,z1,z3,z4,z244,z5,z6])],[(1,[z0,z1,z3,z4,z5,z245]),(0,[z0,z246,z1,z3,z4,z5,z6]),(1,[z0,z163,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z247,z6]),(0,[z0,z153,z1,z14,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z248]),(0,[z249,z1,z250,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z251,z6]),(1,[z0,z252,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z93,z6]),(0,[z0,z153,z1,z3,z4,z52,z6]),(0,[z0,z253,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z186])],[(0,[z254,z0,z1,z3,z4,z5,z6]),(0,[z0,z129,z1,z3,z4,z5,z6]),(0,[z0,z109,z1,z4,z5,z46,z6])],[(0,[z0,z1,z255,z3,z4,z5,z6]),(1,[z256,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z9,z5,z6]),(0,[z0,z1,z3,z4,z5,z257,z6]),(0,[z0,z1,z3,z4,z258,z5,z6]),(0,[z0,z259,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z260,z6]),(0,[z0,z1,z3,z4,z261,z5,z6]),(0,[z0,z1,z3,z4,z5,z262,z6]),(0,[z0,z1,z3,z4,z5,z263,z6]),(0,[z264,z0,z1,z3,z4,z5,z6])],[(0,[z265,z0,z1,z3,z4,z5,z6]),(0,[z0,z266,z1,z12,z3,z5,z6]),(0,[z0,z197,z20,z1,z3,z5,z6]),(0,[z0,z1,z3,z267,z4,z5,z6])],[(0,[z268,z0,z1,z3,z4,z5,z6]),(0,[z269,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z270]),(0,[z0,z1,z3,z271,z4,z5,z6]),(0,[z0,z1,z3,z9,z21,z5,z6]),(0,[z0,z1,z140,z3,z9,z5,z6])],[(0,[z0,z1,z3,z272,z4,z5,z6]),(0,[z166,z0,z20,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z99,z138]),(0,[z0,z1,z3,z4,z5,z273,z6]),(0,[z0,z274,z1,z3,z4,z5,z6])],[(0,[z15,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z70,z4,z5,z6]),(0,[z0,z1,z3,z9,z35,z5,z6]),(0,[z275,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z276])],[(0,[z146,z0,z101,z3,z4,z5,z6])],[(0,[z277,z0,z1,z3,z4,z5,z6]),(0,[z278,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z9,z5,z46,z6])],[(0,[z279,z0,z1,z3,z4,z5,z6]),(1,[z8,z1,z3,z4,z5,z75]),(0,[z0,z1,z3,z4,z280,z5,z6])]],
   [[(1,[z0,z101,z3,z4,z5,z102]),(0,[z0,z281,z1,z3,z4,z5,z6])],[(0,[z0,z101,z106,z3,z4,z5,z6]),(0,[z118,z0,z1,z4,z5,z46,z6])],[(0,[z0,z1,z3,z4,z282,z5,z6]),(0,[z283,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z45,z46,z6]),(0,[z1,z3,z4,z5,z138,z6,z75]),(0,[z0,z1,z3,z4,z5,z138,z241]),(0,[z0,z101,z3,z4,z31,z5,z6]),(0,[z0,z106,z3,z4,z5,z142,z6]),(0,[z0,z1,z3,z4,z284,z5,z6])],[(0,[z58,z0,z1,z3,z70,z5,z6]),(0,[z58,z0,z1,z3,z9,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z285]),(0,[z0,z1,z3,z4,z5,z6,z286]),(0,[z146,z0,z1,z3,z4,z31,z6]),(0,[z0,z1,z3,z4,z287,z5,z6])],[(0,[z288,z0,z1,z3,z4,z5,z6]),(0,[z58,z0,z83,z3,z4,z5,z6]),(1,[z0,z1,z3,z289,z5,z6]),(1,[z135,z1,z3,z4,z21,z6]),(0,[z0,z290,z1,z3,z4,z5,z6]),(0,[z0,z109,z1,z3,z9,z5,z6]),(0,[z291,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z292,z6])],[(0,[z58,z0,z1,z250,z4,z5,z6]),(0,[z161,z0,z1,z293,z4,z5,z6]),(0,[z0,z1,z3,z293,z4,z5,z6]),(0,[z0,z294,z1,z3,z4,z5,z6]),(0,[z295,z0,z1,z3,z4,z5,z6]),(0,[z0,z296,z1,z3,z4,z5,z6])],[(0,[z297,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z9,z5,z6]),(0,[z74,z0,z1,z3,z4,z6,z186]),(0,[z0,z1,z3,z4,z137,z5,z186])],[(0,[z161,z72,z1,z3,z4,z5,z6]),(0,[z0,z298,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z299]),(0,[z0,z109,z1,z3,z300,z5,z6])]],
   [[(1,[z0,z1,z250,z9,z5,z6]),(0,[z161,z0,z71,z3,z4,z5,z6]),(0,[z161,z0,z1,z3,z4,z5,z245]),(0,[z0,z1,z3,z4,z5,z301,z6]),(0,[z44,z0,z1,z3,z9,z5,z6]),(1,[z0,z302,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z303,z6])],[(0,[z161,z0,z1,z3,z130,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z304]),(0,[z76,z0,z20,z1,z3,z5,z6]),(0,[z0,z305,z1,z3,z4,z5,z6]),(0,[z0,z306,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z19,z5,z6]),(1,[z0,z1,z3,z4,z5,z168]),(0,[z0,z307,z1,z3,z4,z5,z6]),(1,[z0,z153,z1,z3,z22,z6])],[(0,[z0,z1,z3,z4,z5,z308,z6]),(0,[z0,z1,z3,z4,z309,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z310]),(0,[z0,z1,z311,z3,z4,z5,z6])],[(0,[z58,z0,z1,z3,z4,z89,z6]),(0,[z312,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z313,z3,z4,z5,z6]),(0,[z0,z1,z314,z3,z4,z5,z6]),(0,[z0,z1,z315,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z316,z6]),(0,[z0,z20,z1,z3,z5,z99,z6]),(0,[z0,z1,z3,z4,z5,z46,z6]),(0,[z0,z1,z173,z3,z4,z5,z6])],[(0,[z0,z1,z317,z3,z4,z5,z6]),(0,[z0,z1,z3,z318,z4,z5,z6]),(0,[z0,z1,z87,z3,z5,z6,z241])],[(0,[z0,z1,z250,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z75,z81]),(0,[z0,z1,z12,z3,z4,z5,z6]),(1,[z0,z266,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z319])],[(1,[z0,z1,z3,z4,z89,z6]),(0,[z1,z250,z3,z62,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z320]),(0,[z118,z0,z1,z3,z9,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z321,z5,z6]),(0,[z146,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z140,z9,z5,z6]),(0,[z74,z0,z1,z3,z9,z5,z6]),(0,[z0,z1,z3,z4,z322,z5,z6]),(0,[z0,z323,z1,z3,z4,z5,z6])],[(0,[z0,z324,z1,z3,z4,z5,z6]),(0,[z118,z0,z1,z250,z4,z5,z6]),(0,[z0,z1,z3,z130,z9,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z325]),(0,[z326,z0,z1,z3,z4,z5,z6])],[(0,[z58,z0,z1,z62,z4,z5,z6])],[(1,[z0,z91,z3,z4,z5,z6]),(0,[z0,z153,z1,z3,z4,z5,z6])],[(0,[z15,z0,z20,z1,z3,z5,z6]),(1,[z0,z1,z64,z9,z5,z6])],[(0,[z0,z1,z327,z3,z4,z5,z6]),(1,[z0,z1,z62,z9,z5,z6]),(0,[z0,z1,z3,z9,z5,z45,z6]),(0,[z0,z302,z1,z3,z5,z45,z6]),(0,[z0,z1,z3,z4,z5,z6,z328]),(0,[z329,z0,z1,z3,z4,z5,z6])],[(1,[z0,z1,z28,z4,z5,z6])],[(0,[z72,z0,z153,z1,z3,z5,z6]),(0,[z0,z30,z1,z3,z4,z164,z6]),(0,[z0,z1,z154,z3,z9,z5,z6]),(0,[z0,z40,z1,z330,z3,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z6,z331]),(0,[z332,z0,z1,z3,z4,z5,z6])],[(0,[z0,z333,z1,z3,z4,z5,z6]),(0,[z161,z0,z1,z3,z4,z5,z69]),(0,[z0,z334,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z335,z6])],[(0,[z0,z1,z3,z4,z5,z336,z6]),(0,[z0,z1,z3,z4,z5,z337,z6]),(0,[z0,z338,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z3,z9,z5,z6])],[(0,[z0,z1,z3,z4,z5,z339,z6]),(0,[z0,z340,z1,z3,z4,z5,z6]),(0,[z341,z0,z1,z3,z4,z5,z6]),(0,[z342,z0,z1,z3,z4,z5,z6])],[(0,[z343,z0,z1,z3,z4,z5,z6]),(0,[z291,z0,z20,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z344,z6]),(0,[z0,z153,z1,z236,z4,z5,z6]),(0,[z345,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z346,z3,z4,z5,z6])],[(0,[z347,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z69,z6]),(0,[z118,z0,z1,z64,z4,z5,z6]),(0,[z0,z170,z1,z3,z9,z5,z6]),(0,[z0,z1,z3,z4,z5,z348,z6])],[(0,[z0,z1,z3,z349,z4,z5,z6]),(0,[z0,z350,z1,z3,z4,z5,z6]),(0,[z118,z0,z1,z62,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z351,z6]),(0,[z0,z1,z3,z4,z128,z5,z6])],[(0,[z0,z1,z3,z352,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z16]),(0,[z0,z1,z3,z353,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z354,z6]),(0,[z161,z0,z1,z103,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z6]),(0,[z0,z1,z3,z51,z9,z5,z6])]],
   [[(0,[z0,z1,z355,z3,z4,z5,z6]),(0,[z356,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z357,z4,z5,z6]),(0,[z0,z1,z358,z3,z4,z5,z6]),(0,[z0,z1,z359,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z360,z6])],[(0,[z0,z1,z3,z4,z233,z5,z6]),(0,[z0,z1,z361,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z362,z5,z6]),(0,[z0,z20,z1,z3,z4,z5,z6]),(0,[z0,z40,z1,z3,z4,z137,z5])],[(0,[z363,z0,z1,z3,z4,z5,z6]),(0,[z364,z0,z1,z3,z4,z5,z6]),(0,[z365,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z366,z3,z4,z5,z6]),(0,[z146,z74,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z9,z5,z80,z6])],[(0,[z0,z49,z3,z4,z31,z5,z6]),(0,[z0,z1,z3,z4,z5,z367,z6]),(0,[z0,z1,z368,z3,z4,z5,z6]),(0,[z0,z1,z121,z140,z3,z5,z6]),(0,[z369,z0,z1,z3,z4,z5,z6])],[(1,[z72,z1,z3,z130,z5,z6]),(0,[z0,z12,z3,z4,z31,z5,z6]),(0,[z0,z20,z370,z1,z3,z5,z6]),(0,[z0,z1,z371,z3,z4,z5,z6])],[(0,[z15,z0,z1,z3,z4,z5,z209]),(0,[z0,z1,z3,z4,z372,z5,z6]),(0,[z0,z1,z250,z3,z373,z5,z6]),(0,[z0,z1,z3,z4,z52,z45,z6]),(0,[z166,z0,z1,z3,z9,z5,z6]),(0,[z0,z1,z3,z4,z176,z5,z6]),(0,[z118,z0,z1,z4,z5,z80,z6])],[(1,[z141,z94,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z374]),(0,[z0,z1,z375,z3,z4,z5,z6]),(0,[z376,z0,z1,z3,z4,z5,z6]),(0,[z0,z109,z1,z13,z4,z5,z6]),(0,[z0,z1,z377,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z378,z6]),(0,[z0,z379,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z380,z5,z6]),(0,[z0,z1,z3,z4,z26,z45,z6]),(0,[z0,z381,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z142,z75]),(0,[z0,z1,z3,z4,z5,z6,z382]),(0,[z146,z0,z20,z1,z3,z5,z6]),(0,[z0,z20,z1,z383,z3,z5,z6]),(0,[z0,z20,z1,z87,z3,z5,z6])],[(0,[z0,z1,z3,z62,z4,z5,z6]),(0,[z0,z370,z1,z3,z4,z5,z6]),(0,[z0,z98,z1,z3,z4,z5,z6])],[(0,[z384,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z385,z6]),(0,[z74,z0,z1,z3,z4,z5,z138]),(0,[z0,z106,z1,z3,z9,z5,z6]),(0,[z386,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z387,z3,z4,z5,z6]),(0,[z0,z1,z388,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z389,z5,z6]),(0,[z146,z0,z3,z4,z5,z164,z6]),(0,[z146,z0,z3,z4,z5,z142,z6]),(0,[z0,z1,z3,z390,z4,z5,z6]),(0,[z0,z1,z13,z3,z4,z46,z6])],[(0,[z0,z391,z1,z3,z4,z5,z6]),(0,[z0,z1,z392,z3,z4,z5,z6]),(0,[z0,z393,z1,z3,z4,z5,z6])],[(0,[z161,z0,z1,z3,z19,z5,z6]),(0,[z135,z1,z3,z4,z21,z5,z6]),(1,[z0,z11,z1,z9,z5,z6]),(0,[z0,z1,z394,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z395]),(0,[z58,z0,z1,z3,z233,z5,z6]),(0,[z0,z1,z396,z3,z4,z5,z6]),(0,[z0,z20,z32,z1,z3,z5,z6]),(0,[z256,z0,z1,z3,z4,z6,z102]),(0,[z221,z0,z1,z3,z9,z5,z6])],[(0,[z397,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z398,z5,z6]),(0,[z399,z0,z1,z3,z4,z5,z6]),(0,[z0,z104,z1,z3,z4,z5,z6]),(0,[z0,z1,z400,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z183]),(0,[z401,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z332,z0,z20,z1,z3,z5,z6]),(0,[z0,z402,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z403,z6]),(0,[z0,z1,z3,z4,z137,z5,z6])],[(0,[z404,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z405,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z80,z6])],[(0,[z0,z1,z3,z4,z5,z406,z6]),(0,[z0,z1,z3,z9,z5,z6,z241]),(0,[z118,z0,z1,z13,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z407]),(0,[z0,z11,z32,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z202,z6])],[(1,[z161,z1,z3,z19,z5,z6]),(0,[z408,z0,z1,z3,z4,z5,z6]),(0,[z409,z0,z1,z3,z4,z5,z6]),(0,[z76,z0,z1,z3,z9,z5,z6])],[(0,[z410,z0,z1,z3,z4,z5,z6]),(0,[z146,z0,z94,z3,z4,z5,z6]),(1,[z0,z1,z3,z176,z5,z6]),(0,[z0,z411,z1,z3,z4,z5,z6]),(1,[z0,z30,z3,z4,z31,z6]),(0,[z412,z0,z1,z3,z4,z5,z6]),(0,[z413,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z414,z6]),(0,[z0,z40,z1,z4,z5,z80,z6])],[(0,[z1,z3,z130,z4,z19,z5,z6]),(0,[z74,z0,z1,z3,z4,z137,z6])]],
   [[(0,[z415,z0,z1,z3,z4,z5,z6]),(0,[z58,z1,z3,z62,z4,z5,z6]),(0,[z416,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z289,z5,z6]),(0,[z0,z1,z140,z3,z4,z5,z80])],[(0,[z0,z1,z417,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z418,z6]),(0,[z0,z1,z3,z4,z5,z419,z6]),(0,[z0,z1,z330,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z52,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z420])],[(0,[z0,z1,z3,z4,z5,z421,z6]),(0,[z0,z1,z3,z4,z422,z5,z6]),(0,[z0,z1,z3,z423,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z424]),(0,[z0,z1,z3,z425,z4,z5,z6]),(0,[z0,z20,z20,z1,z3,z5,z6]),(0,[z0,z20,z1,z3,z5,z124,z6]),(0,[z0,z1,z3,z426,z4,z5,z6])],[(1,[z0,z324,z1,z3,z5,z6]),(0,[z0,z1,z427,z3,z4,z5,z6]),(0,[z0,z1,z4,z9,z5,z46,z6]),(0,[z0,z20,z98,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z26,z5,z6]),(1,[z0,z1,z428,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z429]),(0,[z0,z1,z175,z3,z4,z5,z6])],[(0,[z135,z0,z1,z3,z4,z45,z6]),(0,[z0,z1,z430,z3,z4,z5,z6]),(1,[z0,z106,z3,z4,z5,z142]),(0,[z0,z20,z1,z3,z5,z132,z6]),(0,[z0,z1,z3,z4,z300,z5,z6]),(0,[z0,z1,z3,z4,z5,z431,z6]),(0,[z0,z432,z1,z3,z4,z5,z6])],[(0,[z141,z0,z94,z3,z4,z5,z6]),(0,[z72,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z433,z6]),(0,[z0,z434,z1,z3,z4,z5,z6]),(0,[z0,z1,z87,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z137,z124])],[(0,[z15,z0,z1,z3,z9,z5,z6]),(0,[z0,z1,z64,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z435,z5,z6]),(0,[z0,z436,z1,z3,z4,z5,z6]),(0,[z166,z0,z1,z3,z4,z5,z138]),(1,[z0,z437,z1,z4,z5,z6]),(0,[z0,z1,z438,z3,z4,z5,z6]),(0,[z439,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z140,z3,z4,z137,z5]),(0,[z0,z1,z3,z4,z5,z6,z241]),(0,[z0,z1,z3,z4,z137,z124,z6])],[(0,[z0,z440,z1,z3,z4,z5,z6]),(0,[z441,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z442,z3,z4,z5,z6]),(1,[z0,z1,z330,z3,z5,z6]),(0,[z0,z1,z3,z4,z137,z5,z124])],[(0,[z0,z20,z1,z4,z9,z5,z6])],[(1,[z0,z136,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z443,z6]),(0,[z0,z1,z3,z4,z5,z6,z444]),(0,[z0,z445,z1,z3,z4,z5,z6]),(0,[z0,z1,z446,z3,z4,z5,z6])],[(0,[z0,z1,z447,z3,z4,z5,z6]),(0,[z141,z94,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z33,z5,z6]),(0,[z448,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z449]),(0,[z450,z0,z1,z3,z4,z5,z6]),(1,[z0,z451,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z452,z5,z6]),(0,[z0,z1,z3,z4,z5,z453,z6]),(0,[z0,z1,z3,z4,z5,z454,z6]),(0,[z0,z1,z3,z4,z5,z6,z455]),(0,[z0,z1,z456,z3,z4,z5,z6])],[(0,[z0,z1,z457,z3,z4,z5,z6]),(0,[z458,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z459,z6])],[(0,[z0,z1,z3,z4,z5,z6,z460]),(0,[z0,z1,z3,z4,z5,z461,z6]),(0,[z0,z1,z3,z4,z5,z462,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z6,z463]),(0,[z135,z0,z7,z3,z4,z5,z6]),(0,[z464,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z465,z4,z5,z6]),(0,[z466,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z467,z6]),(0,[z0,z1,z3,z4,z468,z5,z6])],[(0,[z469,z0,z1,z3,z4,z5,z6]),(0,[z470,z0,z1,z3,z4,z5,z6]),(0,[z471,z0,z1,z3,z4,z5,z6]),(0,[z404,z0,z20,z1,z3,z5,z6])],[(0,[z0,z1,z3,z9,z5,z6,z75]),(0,[z146,z0,z12,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z472]),(0,[z0,z1,z3,z51,z4,z22,z6]),(0,[z0,z98,z1,z3,z4,z5,z241])],[(0,[z0,z1,z3,z4,z21,z5,z6]),(1,[z44,z1,z3,z4,z45,z6]),(0,[z76,z0,z1,z77,z3,z5,z6])],[(0,[z0,z473,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z300,z5,z6])],[(0,[z0,z1,z3,z4,z5,z474,z6]),(0,[z0,z1,z3,z4,z35,z5,z6]),(0,[z0,z20,z101,z1,z3,z5,z6]),(0,[z0,z1,z3,z9,z5,z99,z6])],[(0,[z0,z1,z475,z3,z4,z5,z6]),(0,[z476,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z477,z6])],[(1,[z146,z0,z3,z4,z164,z6]),(0,[z0,z1,z3,z478,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z479]),(0,[z0,z1,z3,z428,z4,z5,z6])]],
   [[(1,[z0,z1,z3,z4,z5,z354]),(0,[z0,z1,z3,z4,z5,z6,z245]),(0,[z135,z0,z1,z3,z4,z5,z6]),(0,[z0,z480,z1,z3,z4,z5,z6])],[(1,[z0,z1,z3,z481,z5,z6]),(0,[z0,z1,z12,z3,z9,z5,z6]),(0,[z0,z30,z1,z3,z4,z31,z6]),(0,[z0,z1,z482,z3,z4,z5,z6]),(0,[z0,z1,z483,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z484,z6])],[(0,[z0,z485,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z486]),(0,[z0,z1,z13,z3,z487,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z488])],[(0,[z0,z1,z489,z3,z4,z5,z6])],[(0,[z490,z0,z1,z3,z4,z5,z6]),(1,[z0,z491,z3,z4,z5,z6]),(0,[z0,z20,z1,z3,z130,z5,z6]),(0,[z1,z3,z4,z21,z5,z45,z6]),(0,[z492,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z9,z5,z493,z6]),(0,[z0,z109,z1,z3,z4,z46,z6])],[(0,[z0,z494,z1,z3,z4,z5,z6]),(0,[z249,z0,z1,z3,z4,z5,z6]),(0,[z0,z20,z1,z3,z5,z22,z6]),(0,[z0,z252,z1,z3,z4,z5,z6])],[(0,[z58,z249,z1,z3,z4,z5,z6]),(0,[z72,z0,z20,z1,z3,z5,z6]),(0,[z44,z0,z1,z3,z4,z21,z6]),(0,[z166,z1,z3,z4,z5,z138,z6]),(0,[z0,z1,z495,z3,z4,z5,z6]),(0,[z496,z0,z1,z3,z4,z5,z6]),(0,[z0,z98,z1,z3,z4,z5,z99]),(0,[z0,z1,z3,z497,z4,z5,z6])],[(0,[z0,z1,z3,z4,z172,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z6,z17]),(0,[z0,z1,z3,z4,z5,z6,z75]),(0,[z498,z0,z1,z3,z4,z5,z6]),(0,[z0,z499,z1,z3,z4,z5,z6])],[(0,[z0,z1,z500,z3,z4,z5,z6]),(0,[z501,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z502,z6]),(0,[z0,z503,z1,z3,z4,z5,z6]),(0,[z0,z440,z20,z1,z3,z5,z6]),(1,[z0,z40,z1,z4,z5,z80])],[(0,[z504,z0,z1,z3,z4,z5,z6])],[(1,[z249,z1,z250,z4,z5,z6]),(0,[z72,z1,z3,z130,z4,z5,z6]),(0,[z0,z20,z1,z3,z31,z5,z6]),(0,[z0,z1,z3,z4,z5,z505,z6]),(0,[z0,z1,z3,z4,z5,z99,z6])],[(0,[z141,z0,z1,z3,z4,z5,z6]),(0,[z0,z106,z49,z3,z4,z5,z6]),(0,[z161,z0,z1,z3,z52,z5,z6]),(0,[z0,z1,z506,z3,z4,z5,z6]),(0,[z0,z11,z12,z3,z4,z5,z6]),(0,[z0,z1,z507,z3,z4,z5,z6]),(0,[z0,z20,z1,z3,z235,z5,z6])],[(0,[z0,z1,z3,z4,z5,z508,z6]),(0,[z0,z1,z3,z4,z509,z5,z6]),(0,[z161,z0,z1,z3,z9,z5,z6]),(0,[z0,z20,z1,z3,z5,z164,z6]),(1,[z0,z1,z3,z4,z5,z93]),(0,[z0,z40,z1,z3,z4,z5,z80]),(0,[z0,z1,z3,z4,z5,z6,z510])],[(0,[z0,z1,z3,z4,z5,z75,z241]),(0,[z0,z340,z1,z3,z9,z5,z6]),(1,[z118,z0,z20,z1,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z119])],[(0,[z8,z1,z3,z4,z5,z6,z75]),(0,[z511,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z64,z4,z9,z5,z6]),(0,[z0,z1,z3,z9,z512,z5,z6]),(0,[z0,z1,z4,z26,z5,z46,z6]),(0,[z0,z513,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z514,z6]),(0,[z0,z515,z1,z3,z4,z5,z6]),(0,[z0,z1,z4,z9,z5,z80,z6]),(0,[z74,z0,z1,z3,z4,z5,z186])],[(0,[z516,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z14,z4,z5,z6]),(0,[z0,z1,z3,z51,z52,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z517]),(0,[z0,z1,z3,z4,z5,z518,z6]),(0,[z0,z163,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z519,z6]),(1,[z0,z1,z3,z4,z6,z331]),(0,[z0,z1,z3,z4,z5,z493,z6]),(0,[z0,z1,z3,z4,z520,z5,z6]),(0,[z0,z1,z3,z4,z5,z521,z6])],[(0,[z0,z302,z1,z3,z4,z5,z6]),(0,[z146,z0,z1,z3,z4,z124,z6]),(0,[z0,z20,z1,z3,z5,z6,z102]),(0,[z0,z20,z1,z3,z5,z6,z186]),(0,[z0,z1,z3,z4,z5,z6,z522])],[(0,[z0,z1,z3,z523,z4,z5,z6]),(0,[z76,z0,z104,z3,z4,z5,z6]),(0,[z0,z1,z524,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z61,z46,z6]),(0,[z525,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z526,z3,z4,z5,z6])],[(0,[z0,z11,z1,z3,z4,z5,z6]),(0,[z0,z527,z1,z3,z4,z5,z6]),(0,[z0,z1,z528,z3,z4,z5,z6]),(0,[z0,z20,z30,z1,z3,z5,z6]),(0,[z0,z20,z1,z3,z9,z5,z6])],[(0,[z76,z0,z49,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z45,z6]),(0,[z365,z0,z1,z3,z9,z5,z6])],[(0,[z529,z0,z1,z3,z4,z5,z6]),(0,[z135,z0,z1,z3,z4,z5,z204])]],
   [[(0,[z135,z0,z20,z1,z3,z5,z6]),(1,[z166,z1,z3,z4,z5,z138]),(0,[z0,z1,z3,z4,z5,z6,z530]),(0,[z0,z1,z13,z3,z4,z26,z6]),(1,[z0,z1,z121,z3,z5,z6]),(0,[z0,z531,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z532])],[(0,[z0,z20,z1,z3,z62,z5,z6]),(0,[z0,z1,z3,z4,z137,z5,z75]),(0,[z0,z533,z1,z3,z4,z5,z6]),(1,[z74,z0,z1,z3,z4,z186])],[(0,[z0,z1,z3,z4,z5,z80,z75]),(0,[z0,z1,z3,z4,z534,z5,z6]),(0,[z0,z40,z1,z3,z4,z5,z81])],[(0,[z0,z32,z1,z3,z4,z5,z6]),(0,[z535,z0,z1,z3,z4,z5,z6]),(0,[z0,z536,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z62,z9,z5,z6]),(0,[z0,z537,z1,z3,z4,z5,z6]),(0,[z0,z32,z1,z12,z4,z5,z6]),(1,[z0,z1,z13,z9,z5,z6]),(0,[z0,z98,z1,z3,z9,z5,z6]),(0,[z490,z0,z20,z1,z3,z5,z6]),(1,[z0,z3,z4,z5,z61,z6])],[(0,[z538,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z539,z5,z6]),(0,[z249,z0,z20,z1,z3,z5,z6]),(0,[z540,z0,z1,z3,z4,z5,z6])],[(0,[z0,z0,z1,z3,z4,z5,z6]),(0,[z541,z0,z1,z3,z4,z5,z6]),(0,[z542,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z543,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z544,z6]),(0,[z0,z1,z77,z465,z4,z5,z6]),(0,[z0,z1,z3,z390,z9,z5,z6]),(0,[z0,z153,z20,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z487,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z545]),(0,[z0,z451,z3,z4,z5,z6,z186])],[(0,[z0,z101,z1,z3,z9,z5,z6])]],
   [[(0,[z72,z0,z1,z3,z130,z5,z6]),(0,[z0,z106,z1,z3,z4,z137,z5]),(0,[z0,z20,z1,z3,z3,z5,z6]),(0,[z0,z546,z1,z3,z4,z5,z6])],[(0,[z15,z0,z49,z3,z4,z5,z6]),(0,[z0,z1,z250,z4,z9,z5,z6]),(0,[z0,z20,z1,z12,z3,z5,z6])],[(0,[z547,z0,z1,z3,z4,z5,z6]),(0,[z0,z101,z1,z3,z4,z137,z5]),(0,[z0,z1,z3,z5,z99,z6,z241]),(0,[z0,z548,z1,z3,z4,z5,z6])],[(0,[z0,z549,z1,z3,z4,z5,z6]),(0,[z161,z1,z3,z4,z19,z5,z6]),(0,[z0,z1,z3,z4,z550,z5,z6]),(0,[z0,z1,z3,z4,z551,z5,z6]),(0,[z74,z0,z40,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z552,z6])],[(0,[z141,z0,z20,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z553,z6]),(0,[z0,z1,z3,z4,z5,z554,z6]),(0,[z0,z1,z3,z4,z5,z138,z102])],[(0,[z0,z1,z555,z3,z4,z5,z6]),(0,[z44,z135,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z556,z6]),(0,[z8,z0,z1,z3,z4,z5,z6]),(0,[z557,z0,z1,z3,z4,z5,z6])],[],[(0,[z0,z94,z3,z4,z5,z6,z102]),(0,[z0,z1,z103,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z558,z5,z6]),(0,[z74,z0,z30,z1,z3,z4,z6])]],
   [[(0,[z0,z20,z1,z3,z19,z5,z6]),(0,[z559,z0,z1,z3,z4,z5,z6]),(1,[z0,z7,z3,z4,z5,z6]),(0,[z560,z0,z1,z3,z4,z5,z6]),(0,[z0,z20,z106,z1,z3,z5,z6])],[(0,[z561,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z5,z6]),(0,[z0,z1,z3,z4,z5,z562,z6])],[(0,[z0,z1,z3,z4,z563,z5,z6]),(0,[z0,z106,z1,z3,z4,z5,z102]),(0,[z0,z20,z1,z140,z3,z5,z6])],[(0,[z0,z49,z3,z4,z33,z5,z6]),(0,[z0,z564,z1,z3,z4,z5,z6]),(0,[z0,z565,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z9,z5,z124,z6])],[(0,[z0,z12,z3,z4,z33,z5,z6]),(0,[z0,z20,z1,z77,z3,z5,z6]),(0,[z0,z101,z1,z3,z4,z5,z102]),(0,[z0,z1,z3,z52,z5,z22,z6]),(0,[z0,z98,z1,z28,z4,z5,z6])],[(0,[z566,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z487,z5,z6])],[(0,[z0,z1,z3,z4,z567,z5,z6]),(0,[z0,z568,z1,z3,z4,z5,z6]),(0,[z74,z0,z101,z1,z3,z4,z5]),(0,[z0,z109,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z569,z4,z5,z6])]],
   [[(1,[z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z16]),(0,[z0,z1,z3,z4,z5,z570,z6])],[(0,[z0,z571,z1,z3,z4,z5,z6]),(0,[z72,z0,z1,z3,z9,z5,z6]),(0,[z0,z1,z3,z572,z4,z5,z6]),(0,[z0,z1,z3,z4,z573,z5,z6]),(0,[z0,z1,z3,z4,z5,z574,z6]),(0,[z0,z153,z1,z3,z4,z22,z6]),(0,[z0,z1,z575,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z576,z6]),(0,[z0,z1,z577,z3,z4,z5,z6]),(0,[z0,z1,z64,z3,z9,z5,z6]),(0,[z0,z1,z3,z578,z4,z5,z6])],[(0,[z0,z1,z3,z4,z579,z5,z6]),(0,[z0,z580,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z581,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z582,z6])],[(0,[z0,z49,z3,z4,z35,z5,z6]),(0,[z0,z1,z3,z4,z583,z5,z6]),(0,[z0,z584,z1,z3,z4,z5,z6]),(0,[z0,z32,z3,z4,z31,z5,z6]),(0,[z0,z1,z585,z3,z4,z5,z6])],[(0,[z146,z0,z49,z3,z4,z5,z6]),(0,[z0,z586,z1,z3,z4,z5,z6]),(0,[z0,z20,z94,z1,z3,z5,z6]),(0,[z0,z11,z1,z4,z9,z5,z6]),(0,[z0,z1,z3,z4,z481,z5,z6]),(0,[z0,z1,z3,z4,z5,z587,z6]),(0,[z0,z20,z40,z1,z3,z5,z6]),(0,[z0,z588,z1,z3,z4,z5,z6]),(0,[z589,z0,z1,z3,z4,z5,z6])],[(0,[z0,z590,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z591,z4,z5,z6]),(0,[z146,z0,z1,z3,z4,z164,z6]),(0,[z0,z1,z3,z4,z5,z6,z592])],[]],
   [[(0,[z0,z1,z3,z593,z4,z5,z6]),(0,[z0,z1,z140,z3,z4,z5,z81]),(0,[z0,z1,z3,z4,z594,z5,z6])],[(0,[z0,z1,z3,z4,z373,z5,z6]),(0,[z0,z104,z1,z77,z3,z5,z6]),(0,[z595,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z236,z4,z5,z6]),(0,[z0,z153,z1,z3,z5,z22,z6])],[(0,[z0,z11,z94,z3,z4,z5,z6]),(0,[z58,z0,z196,z3,z4,z5,z6]),(0,[z0,z1,z596,z3,z4,z5,z6]),(0,[z118,z0,z32,z1,z4,z5,z6]),(0,[z76,z0,z1,z3,z35,z5,z6]),(1,[z0,z109,z1,z4,z46,z6]),(0,[z74,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z597,z6]),(0,[z0,z32,z1,z4,z9,z5,z6]),(0,[z0,z598,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z599,z6])],[(0,[z0,z1,z49,z3,z4,z5,z6]),(0,[z600,z0,z1,z3,z4,z5,z6]),(0,[z0,z601,z1,z3,z4,z5,z6]),(1,[z0,z104,z3,z35,z5,z6]),(0,[z0,z1,z3,z4,z602,z5,z6]),(0,[z0,z106,z1,z3,z4,z5,z142])],[(1,[z0,z196,z3,z4,z5,z6]),(0,[z0,z1,z3,z289,z5,z45,z6]),(0,[z8,z0,z20,z1,z3,z5,z6]),(0,[z0,z603,z1,z3,z4,z5,z6]),(0,[z0,z252,z3,z4,z5,z46,z6])],[(0,[z0,z1,z3,z4,z5,z604,z6])],[(1,[z0,z1,z3,z4,z453,z6]),(0,[z0,z1,z3,z4,z5,z142,z138]),(0,[z0,z605,z1,z3,z4,z5,z6]),(0,[z0,z20,z1,z3,z5,z360,z6])]],
   [[(0,[z58,z0,z1,z3,z4,z5,z354]),(0,[z0,z451,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z238,z186])],[(0,[z0,z437,z1,z3,z4,z5,z6]),(0,[z0,z1,z606,z3,z4,z5,z6]),(0,[z0,z1,z607,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z608,z6]),(0,[z0,z109,z1,z3,z4,z26,z6]),(0,[z0,z1,z3,z4,z609,z5,z6])],[(1,[z0,z1,z3,z4,z216,z6]),(0,[z610,z0,z1,z3,z4,z5,z6]),(0,[z0,z20,z1,z3,z5,z138,z6]),(0,[z0,z611,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z612,z6]),(0,[z0,z1,z3,z4,z5,z613,z6]),(0,[z0,z1,z614,z3,z4,z5,z6])],[(0,[z0,z615,z1,z3,z4,z5,z6]),(0,[z0,z88,z1,z13,z3,z5,z6])],[(0,[z0,z1,z250,z3,z9,z5,z6]),(0,[z72,z0,z1,z3,z19,z5,z6]),(0,[z0,z1,z3,z4,z5,z99,z75]),(0,[z0,z1,z616,z3,z4,z5,z6])],[(0,[z0,z1,z617,z3,z4,z5,z6])],[(0,[z0,z1,z3,z618,z4,z5,z6]),(0,[z0,z1,z3,z4,z619,z5,z6]),(0,[z620,z0,z1,z3,z4,z5,z6]),(0,[z146,z0,z1,z3,z9,z5,z6]),(0,[z0,z1,z3,z9,z5,z22,z6]),(0,[z118,z0,z20,z1,z4,z5,z6]),(0,[z0,z109,z20,z1,z3,z5,z6]),(1,[z0,z1,z173,z3,z4,z5])],[(0,[z0,z1,z136,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z204]),(0,[z0,z1,z621,z3,z4,z5,z6]),(0,[z0,z20,z11,z1,z3,z5,z6]),(0,[z0,z1,z622,z3,z4,z5,z6])]],
   [[(0,[z249,z0,z1,z3,z9,z5,z6]),(1,[z0,z1,z3,z373,z5,z6]),(0,[z0,z1,z3,z4,z5,z623,z6]),(0,[z0,z32,z3,z4,z33,z5,z6]),(0,[z0,z1,z3,z4,z624,z5,z6]),(1,[z0,z1,z3,z4,z5,z406]),(0,[z0,z1,z13,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z625,z6])],[(0,[z0,z94,z1,z3,z4,z5,z6]),(0,[z0,z626,z1,z3,z4,z5,z6]),(0,[z0,z153,z1,z3,z9,z5,z6]),(0,[z0,z40,z1,z3,z4,z5,z6])],[(0,[z249,z0,z1,z250,z4,z5,z6]),(0,[z0,z1,z627,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z628,z6]),(0,[z0,z1,z629,z3,z4,z5,z6]),(0,[z0,z630,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z631]),(0,[z0,z632,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z633,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z634]),(1,[z0,z1,z3,z4,z172,z6]),(0,[z635,z0,z1,z3,z4,z5,z6]),(1,[z0,z3,z4,z5,z6,z238])],[(0,[z0,z1,z3,z4,z636,z5,z6]),(0,[z0,z637,z1,z3,z4,z5,z6]),(0,[z0,z1,z12,z3,z481,z5,z6]),(0,[z638,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z639,z6]),(0,[z0,z1,z3,z4,z5,z640,z6]),(0,[z0,z503,z1,z3,z9,z5,z6])],[(0,[z0,z1,z3,z4,z5,z641,z6]),(0,[z0,z437,z1,z77,z4,z5,z6]),(0,[z0,z1,z3,z4,z6,z331,z102]),(0,[z0,z588,z20,z1,z3,z5,z6]),(0,[z642,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z643,z5,z6]),(0,[z0,z1,z3,z644,z4,z5,z6]),(0,[z0,z1,z3,z645,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z646]),(0,[z0,z1,z3,z9,z5,z164,z6]),(0,[z0,z20,z1,z3,z137,z5,z6]),(1,[z0,z1,z140,z4,z5,z81])],[(0,[z141,z0,z1,z3,z9,z5,z6]),(0,[z0,z1,z3,z465,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z647]),(0,[z0,z1,z3,z4,z5,z648,z6])]],
   [[(0,[z0,z649,z1,z3,z4,z5,z6]),(0,[z0,z650,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z651,z6]),(0,[z0,z20,z1,z3,z5,z142,z6]),(0,[z0,z1,z3,z652,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z653,z6])],[(0,[z0,z1,z3,z654,z4,z5,z6]),(0,[z0,z30,z1,z3,z4,z5,z6]),(0,[z0,z20,z1,z3,z5,z6,z81]),(0,[z0,z98,z1,z428,z4,z5,z6])],[(0,[z0,z1,z3,z4,z216,z5,z6]),(0,[z74,z0,z20,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z655]),(0,[z0,z1,z87,z3,z4,z5,z241])],[(0,[z161,z0,z1,z3,z4,z453,z6]),(0,[z0,z1,z3,z656,z4,z5,z6]),(0,[z0,z1,z3,z657,z4,z5,z6]),(0,[z658,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z659])],[(0,[z0,z324,z1,z250,z3,z5,z6]),(0,[z0,z660,z1,z3,z4,z5,z6]),(0,[z0,z1,z661,z3,z4,z5,z6]),(0,[z0,z662,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z9,z5,z6,z102]),(0,[z0,z1,z3,z9,z5,z6,z186])],[(0,[z0,z1,z663,z3,z4,z5,z6])],[(0,[z0,z1,z77,z3,z4,z5,z6]),(0,[z0,z1,z3,z9,z9,z5,z6])],[(0,[z56,z0,z1,z3,z4,z5,z6]),(0,[z249,z0,z1,z62,z4,z5,z6]),(0,[z664,z0,z1,z3,z4,z5,z6]),(0,[z0,z55,z1,z3,z4,z5,z6]),(1,[z0,z1,z9,z5,z46,z6]),(0,[z0,z20,z1,z3,z52,z5,z6]),(1,[z0,z1,z87,z3,z5,z241])]],
   [[(0,[z0,z20,z1,z49,z3,z5,z6]),(0,[z0,z1,z491,z3,z4,z5,z6]),(0,[z0,z1,z665,z3,z4,z5,z6]),(0,[z0,z104,z3,z4,z35,z5,z6]),(0,[z0,z1,z3,z4,z5,z406,z164]),(0,[z0,z1,z223,z3,z4,z5,z6]),(0,[z666,z0,z1,z3,z4,z5,z6])],[(0,[z0,z83,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z168]),(0,[z0,z1,z3,z4,z5,z667,z6]),(0,[z0,z11,z1,z12,z4,z5,z6]),(0,[z74,z0,z106,z1,z3,z4,z5]),(0,[z0,z20,z1,z3,z26,z5,z6]),(0,[z0,z1,z3,z4,z5,z668,z6])],[(1,[z0,z1,z3,z4,z5,z209]),(0,[z0,z669,z1,z3,z4,z5,z6]),(0,[z670,z0,z1,z3,z4,z5,z6]),(0,[z0,z671,z1,z3,z4,z5,z6]),(0,[z0,z266,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z672,z5,z6]),(0,[z0,z1,z3,z4,z673,z5,z6])],[(0,[z161,z0,z491,z3,z4,z5,z6]),(0,[z0,z674,z1,z3,z4,z5,z6]),(0,[z74,z0,z1,z140,z3,z4,z5])],[(0,[z0,z1,z3,z4,z5,z6,z675]),(0,[z0,z1,z3,z4,z5,z676,z6])],[(0,[z0,z1,z3,z4,z5,z677,z6]),(0,[z0,z1,z3,z678,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z679,z6])],[(1,[z0,z1,z293,z4,z5,z6]),(0,[z8,z0,z1,z3,z4,z5,z75]),(0,[z0,z32,z1,z3,z9,z5,z6]),(0,[z0,z1,z3,z4,z680,z5,z6]),(0,[z0,z681,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z682]),(0,[z0,z1,z87,z3,z4,z5,z99]),(0,[z683,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z684]),(0,[z0,z1,z3,z4,z5,z6,z685])]],
   [[(0,[z0,z1,z3,z686,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z687,z6]),(0,[z540,z0,z1,z3,z9,z5,z6]),(0,[z0,z1,z3,z4,z512,z5,z6]),(0,[z0,z1,z3,z4,z5,z688,z6])],[(1,[z0,z71,z3,z4,z5,z6]),(0,[z0,z1,z689,z3,z4,z5,z6]),(0,[z690,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z691,z6]),(0,[z0,z30,z1,z3,z4,z124,z6]),(0,[z0,z1,z383,z3,z4,z5,z6]),(0,[z0,z1,z692,z3,z4,z5,z6])],[(0,[z0,z94,z3,z4,z31,z5,z6]),(0,[z44,z0,z1,z3,z4,z45,z6]),(0,[z0,z1,z3,z4,z693,z5,z6]),(0,[z0,z1,z3,z4,z5,z138,z81]),(0,[z0,z694,z1,z3,z4,z5,z6]),(0,[z0,z20,z1,z3,z33,z5,z6]),(0,[z0,z1,z3,z695,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z102]),(0,[z256,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z696,z5,z6])],[(0,[z0,z1,z3,z4,z697,z5,z6]),(0,[z0,z1,z3,z4,z698,z5,z6]),(0,[z0,z1,z3,z4,z5,z699,z6]),(0,[z0,z1,z3,z4,z5,z700,z6])],[(0,[z0,z1,z3,z4,z4,z5,z6]),(0,[z0,z91,z1,z3,z4,z5,z6]),(0,[z0,z1,z701,z3,z4,z5,z6]),(0,[z702,z0,z1,z3,z4,z5,z6])],[(0,[z0,z20,z1,z250,z3,z5,z6]),(0,[z0,z703,z1,z3,z4,z5,z6]),(0,[z0,z104,z1,z3,z9,z5,z6])],[(0,[z58,z0,z1,z3,z4,z5,z17]),(0,[z0,z704,z1,z3,z4,z5,z6])],[(0,[z705,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z706,z5,z6]),(0,[z0,z1,z140,z3,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z3,z4,z172,z17]),(0,[z0,z1,z3,z4,z216,z69]),(0,[z0,z1,z707,z4,z5,z6]),(0,[z0,z708,z1,z3,z5,z6]),(0,[z0,z1,z709,z4,z5,z6]),(1,[z0,z3,z4,z710,z6]),(0,[z0,z1,z140,z9,z5,z80])],[(0,[z0,z1,z3,z711,z5,z6]),(0,[z0,z712,z3,z4,z5,z6]),(0,[z0,z1,z3,z9,z216,z6]),(0,[z713,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z6,z714]),(0,[z0,z20,z1,z140,z5,z81]),(0,[z0,z109,z1,z47,z46,z6]),(0,[z0,z1,z3,z715,z5,z6]),(0,[z0,z1,z716,z4,z5,z6])],[(0,[z0,z1,z3,z9,z5,z354]),(0,[z0,z717,z3,z4,z5,z6]),(0,[z0,z1,z718,z9,z5,z6])],[(0,[z0,z1,z3,z719,z5,z6]),(0,[z0,z720,z3,z4,z5,z6]),(0,[z0,z1,z103,z4,z453,z6]),(0,[z0,z1,z3,z4,z721,z6]),(1,[z1,z3,z4,z722,z6]),(0,[z0,z1,z3,z723,z5,z6]),(0,[z332,z0,z1,z3,z132,z6]),(0,[z0,z1,z14,z5,z22,z6])],[(0,[z0,z649,z1,z9,z5,z6]),(0,[z0,z1,z3,z724,z5,z6]),(0,[z135,z1,z3,z4,z21,z204]),(0,[z0,z20,z3,z5,z6,z238]),(0,[z0,z1,z3,z5,z725,z6])],[(0,[z0,z196,z3,z4,z89,z6]),(0,[z0,z726,z3,z4,z5,z6]),(0,[z0,z1,z173,z3,z4,z5])],[(0,[z0,z1,z3,z727,z5,z6]),(0,[z0,z491,z3,z9,z5,z6]),(0,[z0,z1,z103,z4,z216,z6]),(0,[z0,z1,z3,z9,z5,z204]),(0,[z0,z1,z728,z4,z5,z6]),(0,[z0,z1,z729,z140,z5,z6]),(0,[z0,z451,z3,z4,z124,z6])],[(0,[z0,z20,z1,z3,z5,z6]),(0,[z0,z20,z1,z3,z5,z16]),(0,[z141,z20,z94,z3,z5,z6]),(0,[z0,z1,z3,z730,z5,z6]),(0,[z0,z1,z3,z4,z5,z406]),(0,[z0,z1,z3,z731,z5,z6])]],
   [[(0,[z0,z1,z3,z732,z5,z6]),(0,[z1,z62,z36,z9,z5,z6]),(0,[z0,z1,z3,z4,z733,z6]),(0,[z44,z1,z3,z4,z722,z6]),(0,[z0,z1,z678,z9,z5,z6]),(0,[z0,z734,z1,z13,z5,z6]),(0,[z0,z1,z140,z9,z137,z5])],[],[(0,[z0,z1,z3,z4,z172,z6]),(0,[z0,z1,z3,z70,z172,z6]),(0,[z0,z3,z4,z5,z6,z238]),(0,[z256,z0,z20,z1,z3,z6]),(0,[z0,z1,z735,z4,z5,z6])],[(0,[z141,z736,z3,z4,z5,z6]),(0,[z0,z83,z3,z4,z172,z6]),(0,[z0,z1,z3,z4,z89,z354]),(0,[z0,z1,z371,z9,z5,z6]),(0,[z0,z40,z1,z9,z5,z80])],[(0,[z0,z1,z9,z45,z46,z6]),(0,[z0,z1,z3,z737,z5,z6])],[(0,[z249,z1,z250,z9,z5,z6]),(1,[z1,z3,z738,z5,z6]),(0,[z0,z739,z3,z4,z5,z6]),(0,[z0,z1,z3,z740,z5,z6]),(0,[z0,z1,z140,z4,z5,z81])],[(0,[z0,z741,z3,z4,z5,z6]),(0,[z0,z742,z3,z4,z5,z6]),(0,[z0,z611,z1,z4,z5,z80])],[(0,[z15,z736,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z6,z743]),(0,[z0,z1,z3,z9,z5,z93]),(0,[z0,z1,z3,z155,z5,z6]),(0,[z0,z1,z744,z3,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z745,z6]),(0,[z0,z1,z3,z4,z5,z746]),(0,[z0,z747,z3,z4,z5,z6]),(0,[z166,z1,z3,z4,z5,z748])],[(0,[z58,z1,z62,z4,z172,z6]),(0,[z0,z1,z3,z749,z5,z6])],[(0,[z0,z1,z3,z750,z5,z6]),(0,[z0,z20,z30,z3,z31,z6]),(1,[z0,z3,z4,z5,z751]),(0,[z0,z1,z3,z41,z5,z6])],[(0,[z0,z1,z3,z4,z5,z752]),(0,[z0,z1,z3,z4,z753,z6]),(0,[z0,z1,z3,z4,z754,z6]),(0,[z0,z1,z14,z9,z5,z6])],[(0,[z0,z1,z755,z3,z5,z6]),(0,[z0,z101,z3,z4,z5,z751]),(0,[z0,z1,z3,z9,z6,z331]),(0,[z0,z1,z154,z9,z5,z80]),(0,[z0,z1,z3,z4,z5,z756])],[(0,[z0,z1,z3,z4,z757,z6]),(0,[z0,z1,z3,z758,z5,z6]),(0,[z0,z1,z3,z4,z5,z759]),(0,[z0,z1,z3,z760,z5,z6]),(0,[z0,z1,z3,z4,z710,z6]),(0,[z0,z1,z729,z9,z5,z6]),(0,[z0,z109,z252,z4,z46,z6])],[(0,[z0,z1,z9,z5,z46,z6]),(0,[z0,z1,z761,z3,z5,z6]),(0,[z0,z1,z87,z3,z5,z241])],[]],
   [[(0,[z15,z20,z49,z3,z5,z6]),(0,[z0,z1,z762,z4,z5,z6]),(0,[z0,z763,z3,z4,z5,z6]),(0,[z0,z20,z1,z293,z5,z6]),(0,[z0,z764,z3,z4,z5,z6]),(0,[z765,z1,z3,z4,z5,z6]),(0,[z0,z153,z1,z3,z725,z6]),(0,[z0,z1,z766,z3,z5,z6])],[(0,[z0,z1,z3,z4,z5,z209]),(0,[z0,z1,z767,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z768]),(0,[z0,z1,z3,z769,z5,z6]),(0,[z0,z1,z3,z770,z5,z6]),(0,[z0,z298,z3,z4,z5,z142]),(0,[z0,z1,z390,z9,z46,z6]),(0,[z0,z771,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z772,z6]),(0,[z0,z1,z3,z4,z5,z773]),(0,[z540,z1,z62,z9,z5,z6]),(0,[z166,z1,z3,z9,z5,z138]),(0,[z0,z1,z3,z774,z5,z6]),(0,[z0,z30,z3,z4,z710,z6])],[(0,[z0,z1,z3,z775,z5,z6]),(1,[z1,z3,z4,z5,z748])],[(0,[z0,z1,z3,z776,z5,z6]),(0,[z0,z32,z176,z33,z5,z6])],[(0,[z0,z1,z293,z4,z5,z6]),(0,[z135,z1,z3,z4,z722,z6]),(0,[z0,z1,z3,z777,z5,z6]),(0,[z0,z40,z1,z4,z5,z653])],[(0,[z0,z1,z3,z4,z5,z778]),(0,[z0,z1,z3,z4,z5,z779]),(0,[z0,z1,z3,z780,z5,z6]),(0,[z0,z153,z1,z3,z132,z6])],[(0,[z0,z1,z4,z5,z781,z6]),(0,[z0,z20,z1,z3,z5,z406]),(0,[z0,z20,z106,z3,z5,z142]),(0,[z0,z503,z3,z128,z5,z6]),(0,[z0,z1,z782,z3,z9,z5])]],
   [[(0,[z0,z71,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z245]),(0,[z0,z1,z783,z4,z5,z6]),(0,[z0,z1,z784,z4,z5,z6]),(0,[z0,z1,z729,z3,z5,z6]),(0,[z0,z785,z3,z4,z5,z6]),(0,[z0,z97,z20,z1,z5,z6])],[(0,[z0,z1,z786,z3,z5,z6]),(0,[z787,z1,z3,z4,z5,z6]),(0,[z256,z0,z101,z3,z4,z6]),(0,[z0,z1,z13,z300,z5,z6])],[(0,[z0,z20,z1,z3,z172,z6])],[(0,[z0,z1,z788,z3,z5,z6]),(0,[z256,z0,z1,z3,z4,z6]),(0,[z0,z1,z121,z28,z5,z6])],[(0,[z0,z500,z3,z4,z31,z6]),(0,[z0,z1,z3,z4,z6,z789]),(0,[z0,z1,z3,z4,z790,z6]),(0,[z1,z250,z62,z9,z5,z6])],[(0,[z413,z1,z3,z4,z5,z75]),(0,[z0,z791,z3,z9,z5,z6]),(0,[z0,z792,z3,z4,z5,z6]),(0,[z74,z0,z1,z3,z4,z431]),(0,[z0,z1,z3,z4,z137,z467])],[(0,[z0,z1,z627,z9,z5,z6]),(0,[z72,z1,z3,z36,z5,z6]),(0,[z291,z440,z1,z3,z5,z6])],[(0,[z0,z1,z3,z4,z5,z793]),(0,[z0,z196,z3,z233,z5,z6]),(0,[z0,z1,z457,z9,z5,z6]),(0,[z0,z1,z3,z794,z5,z6]),(0,[z0,z11,z12,z4,z5,z6]),(0,[z146,z0,z163,z3,z4,z164]),(0,[z0,z1,z3,z4,z5,z751]),(0,[z0,z1,z3,z5,z99,z795])]],
   [[(0,[z0,z1,z3,z70,z5,z17]),(0,[z135,z7,z3,z4,z21,z6]),(0,[z0,z1,z9,z5,z351,z6]),(0,[z0,z20,z1,z661,z5,z6]),(0,[z0,z1,z3,z796,z5,z6])],[(0,[z0,z83,z3,z4,z5,z17]),(0,[z0,z1,z3,z797,z5,z6]),(0,[z0,z1,z3,z4,z124,z798])],[(0,[z0,z1,z3,z799,z5,z6]),(0,[z0,z20,z136,z3,z5,z6]),(0,[z0,z7,z3,z9,z5,z6]),(0,[z0,z32,z4,z33,z5,z6]),(0,[z0,z370,z1,z9,z5,z6])],[(0,[z8,z1,z3,z4,z5,z75]),(0,[z0,z1,z800,z3,z5,z6]),(0,[z0,z163,z3,z4,z31,z5])],[(0,[z161,z1,z3,z19,z453,z6]),(0,[z0,z1,z3,z5,z801,z6]),(0,[z0,z20,z1,z173,z3,z5]),(0,[z0,z109,z4,z61,z46,z6]),(0,[z0,z1,z802,z3,z5,z6])],[(0,[z15,z49,z3,z4,z5,z6]),(0,[z15,z49,z3,z4,z5,z16]),(0,[z0,z9,z5,z61,z46,z6]),(0,[z0,z1,z140,z155,z5,z81])],[(0,[z0,z1,z3,z4,z803,z6]),(0,[z0,z20,z1,z210,z5,z6]),(0,[z0,z7,z3,z4,z5,z168]),(0,[z0,z1,z804,z4,z5,z6]),(0,[z0,z3,z4,z31,z710,z6]),(0,[z118,z0,z252,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z805]),(0,[z0,z1,z689,z9,z5,z6]),(0,[z0,z1,z806,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z807])]],
   [[(0,[z135,z1,z3,z4,z21,z6]),(0,[z0,z1,z808,z4,z5,z6])],[(0,[z0,z20,z1,z3,z5,z209]),(0,[z0,z1,z3,z4,z5,z69]),(0,[z0,z1,z809,z4,z5,z6])],[(0,[z0,z1,z3,z9,z5,z6]),(0,[z0,z1,z3,z810,z5,z6]),(0,[z0,z1,z3,z9,z5,z16]),(0,[z0,z1,z3,z70,z5,z6]),(0,[z0,z1,z811,z4,z5,z6]),(0,[z0,z11,z223,z9,z5,z6]),(1,[z0,z1,z173,z9,z5]),(0,[z0,z1,z3,z812,z5,z6]),(0,[z0,z1,z4,z5,z813,z81]),(0,[z0,z1,z3,z814,z5,z6])],[(0,[z0,z83,z3,z4,z5,z6]),(0,[z0,z83,z3,z70,z5,z6]),(0,[z342,z1,z3,z4,z21,z6]),(0,[z0,z3,z4,z5,z751,z102]),(0,[z0,z1,z394,z9,z5,z6])],[(0,[z0,z436,z1,z9,z5,z6]),(0,[z0,z1,z3,z4,z5,z815]),(0,[z161,z491,z3,z19,z5,z6]),(0,[z146,z0,z3,z4,z406,z164])],[(0,[z0,z1,z3,z233,z172,z6]),(0,[z0,z55,z383,z3,z5,z6]),(0,[z0,z1,z3,z816,z5,z6]),(0,[z0,z98,z1,z3,z5,z99]),(0,[z0,z1,z817,z3,z5,z6])],[(0,[z0,z1,z3,z4,z5,z168]),(0,[z0,z194,z1,z9,z5,z6]),(0,[z0,z20,z1,z3,z5,z778]),(0,[z0,z153,z1,z3,z22,z6])],[(0,[z0,z1,z103,z4,z5,z6]),(0,[z0,z106,z3,z4,z5,z521]),(0,[z0,z170,z1,z3,z5,z99]),(0,[z0,z1,z4,z5,z818,z6])]],
   [[(0,[z0,z20,z1,z3,z5,z245]),(0,[z0,z1,z174,z9,z5,z6]),(0,[z0,z1,z3,z819,z5,z6])],[(0,[z58,z1,z62,z70,z5,z6]),(0,[z58,z1,z62,z9,z5,z6]),(0,[z0,z820,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z93,z61])],[(0,[z0,z494,z1,z9,z5,z6]),(0,[z0,z821,z1,z3,z4,z5]),(0,[z58,z83,z62,z4,z5,z6]),(0,[z0,z822,z3,z4,z5,z6]),(0,[z0,z1,z823,z4,z5,z6]),(0,[z0,z266,z1,z3,z5,z6]),(0,[z0,z1,z3,z47,z5,z6]),(0,[z0,z3,z4,z5,z6,z824])],[(0,[z0,z1,z3,z4,z89,z6]),(0,[z58,z1,z825,z4,z5,z6]),(0,[z0,z1,z9,z5,z553,z6]),(0,[z1,z3,z4,z5,z138,z748]),(0,[z642,z1,z3,z4,z5,z138]),(0,[z0,z20,z163,z1,z3,z5]),(0,[z0,z1,z9,z5,z80,z6]),(0,[z0,z1,z236,z9,z5,z6]),(0,[z0,z88,z1,z236,z5,z6])],[(0,[z0,z109,z1,z9,z46,z6]),(0,[z0,z451,z3,z4,z137,z5])],[(0,[z0,z1,z3,z826,z5,z6]),(0,[z0,z827,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z795]),(0,[z0,z828,z3,z4,z5,z6])],[(0,[z0,z829,z3,z4,z5,z6])],[(0,[z0,z91,z3,z4,z5,z6]),(0,[z0,z106,z3,z4,z5,z751]),(0,[z0,z1,z3,z4,z725,z6])]],
   [[(0,[z0,z830,z3,z4,z5,z6]),(0,[z0,z1,z396,z9,z5,z6]),(0,[z0,z1,z3,z52,z453,z6]),(0,[z291,z1,z3,z130,z5,z6]),(0,[z256,z0,z101,z3,z4,z5]),(1,[z74,z0,z451,z3,z4]),(0,[z0,z1,z3,z4,z137,z798])],[(0,[z0,z1,z3,z4,z5,z831]),(0,[z0,z1,z832,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z833])],[(0,[z0,z1,z3,z4,z5,z834]),(0,[z58,z1,z62,z4,z89,z6]),(0,[z0,z1,z3,z4,z5,z835]),(0,[z0,z3,z4,z5,z142,z751]),(0,[z0,z1,z28,z4,z5,z6])],[(0,[z0,z1,z836,z4,z5,z6]),(0,[z0,z1,z825,z4,z5,z6]),(0,[z0,z302,z1,z3,z453,z6]),(0,[z0,z136,z3,z4,z5,z204]),(0,[z8,z20,z1,z3,z5,z75]),(0,[z0,z1,z87,z3,z5,z795])],[(0,[z0,z1,z3,z837,z5,z6]),(0,[z146,z0,z3,z4,z10,z6]),(0,[z0,z197,z1,z9,z5,z6]),(0,[z0,z1,z173,z9,z5,z46])],[(0,[z0,z1,z3,z838,z5,z6]),(0,[z0,z1,z116,z9,z5,z6]),(0,[z839,z1,z3,z4,z5,z6])],[(0,[z0,z1,z840,z4,z5,z6]),(0,[z0,z1,z3,z841,z5,z6]),(0,[z439,z1,z3,z4,z5,z75]),(0,[z0,z1,z842,z4,z5,z6]),(0,[z0,z734,z1,z3,z5,z6]),(0,[z0,z170,z1,z3,z5,z202]),(0,[z0,z843,z3,z4,z5,z6])],[(0,[z0,z302,z1,z740,z5,z6]),(0,[z0,z55,z1,z465,z5,z6]),(0,[z0,z1,z9,z5,z431,z6]),(0,[z0,z844,z3,z4,z5,z6])]],
   [[(0,[z135,z20,z1,z3,z21,z6]),(0,[z0,z1,z483,z9,z5,z6]),(0,[z0,z252,z9,z5,z46,z6]),(0,[z0,z3,z4,z5,z6,z845])],[(0,[z0,z20,z1,z3,z5,z69]),(0,[z0,z846,z1,z3,z5,z6])],[(0,[z0,z20,z1,z103,z5,z6]),(0,[z0,z1,z3,z4,z5,z847]),(0,[z1,z3,z4,z21,z722,z6]),(0,[z0,z1,z848,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z849]),(0,[z0,z1,z3,z9,z5,z406]),(0,[z0,z1,z237,z9,z5,z6]),(0,[z0,z340,z1,z3,z493,z6]),(0,[z0,z850,z3,z4,z5,z6]),(0,[z0,z851,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z852]),(0,[z0,z1,z3,z4,z853,z6]),(0,[z0,z197,z1,z3,z5,z119])],[(0,[z0,z163,z1,z3,z9,z5]),(0,[z0,z854,z3,z4,z5,z6])],[(0,[z0,z1,z3,z9,z172,z6]),(0,[z0,z1,z3,z855,z5,z6]),(0,[z0,z1,z65,z9,z5,z6])],[(0,[z0,z71,z293,z4,z5,z6]),(0,[z0,z1,z293,z4,z5,z245]),(0,[z0,z20,z1,z3,z5,z168]),(0,[z0,z1,z3,z856,z5,z6]),(0,[z0,z848,z3,z4,z5,z6]),(0,[z0,z1,z400,z9,z5,z6]),(0,[z118,z0,z1,z173,z4,z5])],[(0,[z0,z1,z3,z857,z5,z6]),(0,[z0,z1,z3,z4,z858,z6]),(0,[z0,z1,z293,z130,z5,z6]),(0,[z256,z0,z1,z3,z9,z6]),(0,[z0,z588,z1,z9,z5,z6]),(0,[z0,z1,z388,z9,z5,z6]),(0,[z0,z1,z140,z123,z4,z5])]],
   [[(0,[z0,z1,z116,z3,z5,z6]),(0,[z0,z1,z140,z9,z5,z81]),(0,[z0,z173,z3,z4,z5,z61])],[(0,[z736,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z859,z5,z6]),(0,[z72,z1,z3,z130,z5,z6]),(0,[z0,z71,z3,z4,z5,z245]),(0,[z0,z860,z1,z4,z5,z6]),(0,[z0,z1,z428,z5,z99,z6])],[(0,[z0,z1,z3,z861,z5,z6]),(0,[z0,z564,z1,z9,z5,z6]),(0,[z0,z1,z3,z862,z5,z6]),(0,[z0,z603,z1,z3,z5,z99]),(0,[z0,z568,z3,z4,z5,z102]),(0,[z0,z20,z1,z236,z5,z6]),(0,[z0,z1,z3,z4,z818,z6]),(0,[z74,z0,z451,z3,z4,z186])],[(0,[z0,z1,z3,z233,z5,z17]),(0,[z0,z20,z1,z3,z89,z6]),(0,[z863,z0,z1,z4,z5,z6]),(0,[z0,z20,z1,z28,z5,z6]),(0,[z0,z109,z1,z173,z4,z46])],[(0,[z0,z1,z3,z5,z864,z6]),(0,[z0,z1,z865,z3,z5,z6]),(1,[z146,z0,z163,z3,z4])],[(0,[z0,z1,z866,z4,z5,z6]),(0,[z0,z1,z9,z5,z604,z6]),(0,[z0,z1,z3,z867,z5,z6])],[(0,[z0,z1,z868,z4,z5,z6]),(0,[z0,z1,z272,z9,z5,z6]),(0,[z0,z869,z3,z4,z5,z6]),(0,[z0,z98,z1,z3,z5,z795])],[(0,[z15,z49,z3,z4,z5,z209]),(0,[z0,z175,z3,z4,z5,z6]),(0,[z0,z20,z491,z3,z5,z6]),(0,[z0,z870,z1,z3,z4,z6]),(0,[z0,z1,z3,z9,z5,z756])]],
   [[(0,[z0,z150,z1,z9,z5,z6]),(0,[z871,z0,z1,z3,z4,z5]),(0,[z0,z872,z3,z4,z5,z6]),(0,[z0,z873,z3,z4,z5,z6])],[(0,[z0,z302,z1,z3,z52,z6]),(0,[z0,z11,z1,z9,z5,z6]),(0,[z0,z189,z1,z9,z5,z6]),(0,[z256,z0,z101,z1,z3,z4]),(0,[z0,z1,z9,z5,z613,z6]),(0,[z0,z1,z3,z4,z5,z874])],[(0,[z0,z875,z1,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z876]),(0,[z0,z584,z1,z9,z5,z6]),(0,[z877,z1,z3,z4,z5,z6]),(1,[z256,z0,z101,z3,z4])],[(0,[z0,z1,z3,z4,z878,z6]),(0,[z0,z879,z3,z4,z5,z6]),(0,[z0,z1,z9,z5,z484,z6])],[(0,[z0,z1,z3,z9,z5,z209]),(0,[z0,z1,z880,z3,z5,z6]),(0,[z256,z0,z1,z3,z4,z75]),(0,[z0,z3,z4,z31,z126,z6]),(0,[z0,z860,z1,z64,z5,z6]),(0,[z0,z771,z3,z9,z5,z6]),(0,[z0,z1,z9,z5,z6,z488]),(0,[z0,z1,z3,z4,z5,z881])],[(0,[z0,z1,z3,z233,z5,z6]),(0,[z0,z3,z4,z5,z6,z882])],[(0,[z256,z0,z94,z3,z4,z6]),(0,[z0,z83,z3,z233,z5,z6])],[(0,[z0,z1,z250,z233,z5,z6]),(0,[z0,z1,z293,z4,z5,z69]),(0,[z0,z1,z9,z5,z623,z6]),(0,[z0,z1,z140,z41,z5,z6]),(1,[z0,z1,z4,z5,z813])]],
   [[(0,[z0,z1,z293,z9,z5,z6]),(0,[z161,z1,z3,z19,z5,z6]),(0,[z0,z32,z116,z33,z5,z6]),(0,[z0,z1,z3,z4,z137,z587]),(0,[z0,z883,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z884]),(0,[z0,z1,z3,z885,z5,z6]),(0,[z0,z1,z3,z176,z5,z6]),(0,[z0,z1,z4,z5,z813,z6]),(0,[z0,z886,z1,z3,z5,z6])],[(0,[z0,z1,z887,z3,z4,z5]),(0,[z0,z888,z1,z250,z5,z6]),(0,[z0,z71,z3,z4,z5,z69]),(0,[z0,z55,z1,z9,z5,z6]),(0,[z0,z1,z3,z4,z5,z889]),(0,[z0,z1,z526,z9,z5,z6])],[(0,[z0,z71,z3,z9,z5,z6]),(0,[z0,z1,z3,z9,z5,z245]),(0,[z0,z163,z1,z3,z4,z5])],[(0,[z0,z1,z3,z4,z5,z890]),(0,[z0,z49,z3,z4,z5,z16]),(0,[z58,z1,z62,z233,z5,z6]),(0,[z0,z891,z3,z4,z5,z6]),(0,[z0,z252,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z892]),(0,[z0,z1,z95,z9,z5,z6]),(0,[z0,z1,z96,z9,z5,z6]),(0,[z0,z1,z3,z4,z798,z186])],[(0,[z0,z20,z1,z181,z5,z6]),(0,[z0,z1,z3,z4,z5,z893]),(0,[z0,z1,z894,z4,z5,z6]),(0,[z0,z1,z9,z5,z505,z6])],[(0,[z0,z1,z3,z4,z895,z6]),(0,[z0,z896,z1,z3,z4,z6]),(0,[z0,z101,z622,z3,z4,z5]),(0,[z0,z20,z860,z1,z5,z6]),(0,[z0,z20,z252,z3,z5,z6]),(0,[z0,z1,z87,z428,z5,z6]),(1,[z0,z1,z3,z5,z795])],[(0,[z0,z324,z1,z3,z5,z6]),(0,[z0,z20,z1,z3,z858,z6])]],
   [[(0,[z0,z71,z103,z4,z5,z6]),(0,[z0,z1,z103,z4,z5,z245]),(0,[z0,z1,z3,z4,z5,z897]),(0,[z0,z104,z383,z3,z5,z6]),(0,[z74,z0,z580,z1,z3,z4])],[(0,[z74,z0,z1,z3,z4,z107]),(0,[z0,z1,z430,z9,z5,z6])],[(0,[z0,z32,z160,z4,z5,z6]),(0,[z0,z11,z12,z9,z5,z6]),(0,[z0,z1,z123,z9,z5,z6])],[(0,[z256,z0,z49,z3,z4,z6]),(0,[z0,z898,z3,z4,z5,z6]),(0,[z0,z1,z3,z9,z5,z17]),(0,[z161,z0,z1,z14,z5,z6]),(0,[z0,z1,z899,z3,z5,z6]),(0,[z0,z1,z900,z4,z5,z6]),(0,[z0,z1,z154,z3,z5,z183]),(0,[z74,z0,z3,z4,z238,z186])],[(0,[z476,z49,z3,z4,z5,z6]),(0,[z0,z1,z62,z233,z5,z6]),(0,[z0,z20,z7,z3,z5,z6]),(1,[z0,z252,z9,z5,z6])],[(0,[z0,z3,z4,z5,z901,z6]),(0,[z0,z1,z3,z4,z722,z6]),(0,[z0,z1,z3,z4,z5,z902]),(0,[z0,z1,z330,z3,z5,z6])],[(0,[z0,z903,z1,z3,z5,z6]),(0,[z0,z1,z355,z4,z26,z6]),(0,[z146,z0,z3,z4,z710,z6]),(0,[z0,z1,z13,z9,z46,z6]),(0,[z0,z1,z3,z4,z5,z904])],[(0,[z0,z136,z3,z4,z5,z6]),(0,[z146,z0,z3,z4,z205,z6]),(0,[z0,z101,z3,z4,z5,z102]),(0,[z0,z109,z1,z4,z93,z46])]],
   [[(0,[z15,z49,z3,z9,z5,z6]),(0,[z0,z1,z3,z905,z5,z6]),(0,[z0,z1,z3,z4,z5,z906])],[(0,[z94,z736,z3,z4,z5,z6]),(0,[z0,z20,z71,z3,z5,z6]),(0,[z72,z1,z3,z82,z5,z6]),(0,[z0,z20,z1,z578,z5,z6]),(0,[z0,z20,z1,z3,z5,z874])],[(0,[z161,z1,z3,z19,z216,z6]),(0,[z0,z1,z3,z907,z5,z6]),(0,[z0,z3,z4,z5,z6,z751]),(0,[z0,z1,z9,z5,z6,z532])],[(0,[z0,z1,z293,z19,z5,z6]),(0,[z0,z1,z908,z4,z5,z6]),(0,[z0,z1,z3,z289,z5,z6]),(0,[z135,z1,z3,z9,z21,z6])],[(0,[z0,z1,z3,z4,z89,z17]),(0,[z0,z1,z3,z9,z5,z69]),(0,[z0,z1,z9,z5,z80,z75]),(0,[z0,z1,z173,z9,z5,z6])],[],[(0,[z412,z49,z3,z4,z5,z6]),(0,[z0,z83,z3,z9,z5,z6])],[(0,[z0,z1,z250,z9,z5,z6]),(0,[z0,z302,z1,z3,z5,z6]),(0,[z0,z1,z3,z738,z5,z6]),(0,[z44,z1,z3,z4,z45,z6]),(0,[z135,z1,z3,z4,z21,z168]),(0,[z1,z3,z9,z5,z909,z6]),(0,[z0,z1,z9,z5,z688,z6]),(0,[z0,z1,z3,z725,z22,z6])]],
   [[(0,[z1,z3,z4,z5,z722,z6]),(0,[z0,z1,z3,z4,z910,z6]),(0,[z0,z1,z911,z3,z5,z6]),(0,[z0,z1,z3,z300,z5,z6]),(0,[z0,z20,z912,z3,z5,z6]),(0,[z0,z20,z1,z428,z5,z6])],[(0,[z0,z1,z103,z4,z5,z69]),(0,[z0,z1,z3,z9,z5,z168]),(0,[z0,z1,z3,z9,z5,z913])],[(0,[z0,z1,z3,z914,z5,z6]),(0,[z0,z915,z3,z4,z5,z6]),(0,[z0,z1,z103,z9,z5,z6]),(0,[z0,z916,z3,z4,z5,z6]),(0,[z0,z104,z1,z465,z5,z6]),(0,[z0,z1,z3,z4,z5,z917]),(0,[z0,z252,z173,z3,z4,z5])],[(0,[z146,z0,z3,z4,z164,z6])],[(0,[z0,z1,z3,z4,z5,z354]),(0,[z918,z1,z3,z4,z5,z6]),(0,[z0,z1,z919,z4,z5,z6]),(0,[z0,z1,z154,z3,z5,z241]),(0,[z118,z0,z860,z1,z5,z6]),(0,[z74,z0,z20,z1,z3,z186]),(0,[z0,z1,z3,z4,z6,z798])],[(0,[z0,z920,z1,z3,z5,z6]),(0,[z0,z20,z921,z3,z5,z6])],[(0,[z0,z1,z922,z4,z5,z6]),(0,[z0,z1,z3,z70,z89,z6]),(0,[z0,z1,z3,z9,z89,z6]),(0,[z0,z923,z1,z3,z5,z6]),(0,[z0,z1,z192,z9,z5,z6]),(0,[z0,z32,z1,z481,z5,z6]),(0,[z0,z1,z924,z4,z5,z6]),(0,[z0,z734,z1,z9,z5,z6]),(0,[z74,z0,z1,z3,z9,z186])],[(0,[z0,z1,z3,z4,z925,z6]),(0,[z0,z83,z3,z4,z89,z6]),(0,[z0,z1,z9,z5,z10,z6]),(0,[z0,z1,z140,z9,z5,z6]),(0,[z0,z3,z4,z5,z926,z6])]],
   [[(0,[z0,z491,z3,z4,z5,z6]),(0,[z72,z0,z1,z14,z5,z6]),(0,[z1,z3,z4,z5,z748,z6]),(0,[z0,z1,z9,z5,z24,z6]),(0,[z0,z170,z1,z4,z5,z80]),(0,[z0,z98,z1,z3,z5,z360])],[(0,[z0,z927,z3,z4,z5,z6]),(0,[z0,z153,z1,z236,z22,z6]),(0,[z0,z98,z1,z28,z5,z99])],[(0,[z0,z106,z3,z4,z5,z378]),(0,[z0,z928,z3,z4,z5,z6]),(0,[z161,z294,z1,z3,z5,z6]),(0,[z0,z32,z9,z31,z5,z6]),(0,[z0,z109,z1,z300,z46,z6]),(0,[z0,z929,z3,z4,z5,z6])],[(0,[z58,z1,z62,z4,z5,z354]),(0,[z0,z1,z930,z4,z5,z6]),(0,[z0,z1,z64,z9,z5,z6])],[(0,[z0,z1,z62,z9,z5,z6]),(0,[z525,z1,z3,z4,z45,z6]),(0,[z0,z931,z1,z3,z5,z6]),(0,[z0,z252,z4,z9,z5,z6]),(0,[z0,z1,z3,z4,z5,z813])],[(0,[z0,z932,z1,z3,z5,z6]),(0,[z118,z0,z324,z1,z5,z6]),(0,[z0,z764,z4,z33,z5,z6]),(0,[z0,z1,z28,z9,z5,z6]),(0,[z0,z40,z1,z4,z5,z80]),(0,[z0,z933,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z934,z6]),(0,[z0,z1,z935,z3,z5,z6]),(0,[z0,z1,z665,z9,z5,z6]),(0,[z0,z20,z1,z3,z5,z904])],[(0,[z0,z1,z3,z936,z5,z6]),(0,[z0,z1,z937,z3,z4,z5]),(0,[z0,z101,z3,z4,z5,z111]),(0,[z0,z20,z253,z1,z5,z6])]],
   [[(0,[z0,z20,z196,z3,z5,z6]),(0,[z0,z1,z3,z938,z5,z6]),(0,[z0,z20,z175,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z939]),(0,[z0,z1,z940,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z941])],[(0,[z0,z736,z3,z4,z5,z6]),(0,[z0,z196,z3,z4,z5,z354]),(0,[z1,z3,z738,z19,z5,z6]),(0,[z0,z1,z3,z5,z6,z942]),(0,[z0,z943,z1,z3,z5,z6]),(0,[z0,z1,z255,z4,z5,z81]),(0,[z0,z1,z3,z4,z5,z93])],[(0,[z0,z1,z3,z4,z5,z944]),(0,[z0,z20,z83,z3,z5,z6]),(0,[z0,z945,z3,z4,z5,z6]),(0,[z946,z1,z3,z4,z5,z6]),(0,[z0,z1,z9,z5,z570,z6]),(0,[z0,z1,z9,z5,z79,z6]),(0,[z0,z3,z9,z5,z61,z6])],[(0,[z0,z20,z1,z225,z5,z6])],[(0,[z0,z232,z3,z35,z5,z6]),(0,[z0,z1,z3,z4,z5,z947]),(0,[z0,z1,z3,z4,z5,z948]),(0,[z0,z1,z9,z5,z90,z6]),(0,[z0,z1,z3,z949,z5,z6]),(0,[z0,z1,z495,z9,z5,z6]),(0,[z0,z1,z9,z5,z93,z46])],[(0,[z212,z1,z3,z4,z5,z138]),(0,[z0,z11,z503,z9,z5,z6]),(0,[z0,z1,z950,z4,z5,z6])],[(0,[z0,z1,z951,z4,z5,z6]),(0,[z0,z952,z3,z4,z5,z6]),(0,[z161,z1,z293,z19,z5,z6]),(0,[z0,z1,z3,z4,z6,z331]),(0,[z0,z1,z140,z4,z5,z813])],[(0,[z0,z953,z3,z4,z5,z6]),(0,[z0,z491,z3,z4,z453,z6]),(0,[z44,z20,z1,z3,z45,z6]),(0,[z76,z0,z1,z465,z5,z6]),(0,[z0,z129,z1,z9,z5,z6]),(0,[z0,z20,z954,z3,z5,z6])]],
   [[(0,[z0,z175,z3,z4,z5,z75]),(0,[z74,z0,z1,z3,z4,z205]),(0,[z0,z955,z3,z4,z5,z6]),(0,[z0,z1,z14,z51,z5,z6])],[(0,[z161,z71,z3,z19,z5,z6]),(0,[z161,z1,z3,z19,z5,z245]),(0,[z0,z32,z764,z4,z5,z6]),(0,[z0,z503,z3,z35,z5,z6]),(0,[z0,z3,z9,z5,z956,z6]),(0,[z0,z957,z3,z4,z5,z6])],[(0,[z0,z491,z3,z4,z216,z6]),(0,[z161,z1,z3,z738,z5,z6]),(0,[z0,z958,z3,z4,z5,z6]),(0,[z0,z959,z3,z4,z5,z6]),(0,[z0,z1,z960,z3,z5,z6]),(0,[z0,z20,z1,z14,z5,z6]),(0,[z0,z1,z41,z5,z80,z6])],[(0,[z0,z1,z3,z4,z5,z961]),(0,[z0,z1,z3,z4,z962,z6]),(0,[z0,z1,z3,z4,z963,z6]),(0,[z0,z1,z3,z964,z5,z6]),(0,[z8,z175,z3,z4,z5,z75]),(0,[z965,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z966])],[(0,[z0,z11,z94,z9,z5,z6]),(0,[z0,z1,z3,z4,z5,z967]),(0,[z0,z153,z1,z3,z453,z6]),(0,[z0,z860,z1,z9,z5,z6])],[(0,[z0,z1,z3,z52,z628,z6]),(0,[z0,z1,z3,z968,z5,z6]),(0,[z74,z0,z1,z3,z4,z186])],[(0,[z141,z94,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z969]),(0,[z0,z1,z970,z4,z5,z6]),(0,[z0,z971,z1,z3,z5,z6])],[(0,[z0,z1,z3,z4,z172,z354]),(0,[z0,z1,z3,z4,z972,z6]),(0,[z0,z1,z3,z973,z5,z6]),(0,[z226,z1,z3,z4,z5,z75]),(0,[z0,z11,z266,z12,z5,z6]),(0,[z0,z252,z1,z9,z5,z6])]],
   [[(0,[z0,z3,z4,z5,z61,z6]),(0,[z0,z20,z101,z3,z5,z102]),(0,[z0,z1,z3,z974,z5,z6])],[(0,[z0,z1,z3,z4,z5,z975]),(0,[z0,z976,z1,z4,z5,z6]),(0,[z0,z40,z1,z4,z5,z813])],[(0,[z0,z1,z3,z4,z977,z6]),(0,[z0,z978,z3,z4,z5,z6]),(0,[z0,z175,z3,z9,z5,z6]),(0,[z0,z1,z3,z979,z5,z6])],[(0,[z0,z1,z3,z5,z6,z980]),(0,[z0,z1,z9,z5,z608,z6]),(0,[z0,z1,z3,z4,z981,z6]),(0,[z74,z0,z451,z3,z4,z5])],[],[(0,[z0,z1,z3,z4,z5,z982])],[],[(0,[z249,z1,z250,z373,z5,z6]),(0,[z0,z324,z1,z9,z5,z6]),(0,[z0,z32,z1,z718,z5,z6]),(0,[z0,z860,z1,z3,z5,z6]),(0,[z0,z1,z3,z9,z5,z881])]],
   [[(0,[z0,z1,z3,z4,z5,z983]),(0,[z0,z1,z173,z4,z9,z5])],[(0,[z0,z11,z49,z9,z5,z6]),(0,[z0,z1,z3,z5,z795,z6])],[(0,[z0,z1,z293,z52,z5,z6]),(0,[z161,z1,z3,z19,z5,z69]),(0,[z0,z20,z40,z1,z5,z80])],[(0,[z0,z1,z984,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z985]),(0,[z0,z11,z110,z4,z5,z6]),(0,[z0,z20,z437,z1,z5,z6]),(0,[z0,z30,z3,z4,z31,z6]),(0,[z0,z20,z1,z3,z5,z947])],[(0,[z0,z986,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z987,z6]),(0,[z0,z988,z3,z4,z5,z6])],[(0,[z0,z20,z1,z3,z6,z331]),(0,[z0,z1,z9,z5,z640,z6]),(0,[z0,z340,z1,z4,z46,z6]),(0,[z0,z20,z763,z3,z5,z6]),(0,[z0,z98,z1,z428,z5,z99]),(0,[z74,z0,z1,z3,z4,z798])],[(0,[z0,z1,z3,z989,z5,z6]),(0,[z409,z94,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z990,z6]),(0,[z72,z1,z3,z738,z5,z6]),(0,[z0,z252,z3,z9,z5,z6])]],
   [[(0,[z161,z1,z103,z19,z5,z6]),(0,[z146,z0,z32,z9,z5,z6])],[(0,[z0,z1,z3,z233,z89,z6]),(0,[z0,z1,z991,z3,z4,z5]),(0,[z0,z1,z9,z5,z648,z6]),(0,[z0,z1,z3,z487,z5,z6]),(1,[z0,z1,z3,z4,z798])],[(0,[z0,z324,z1,z103,z5,z6]),(0,[z0,z1,z3,z992,z5,z6]),(0,[z0,z1,z9,z5,z653,z6]),(0,[z0,z1,z428,z4,z5,z6]),(0,[z0,z1,z993,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z994])],[(0,[z1,z825,z62,z4,z5,z6]),(0,[z0,z995,z3,z4,z5,z6]),(0,[z0,z996,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z997]),(0,[z0,z1,z13,z9,z26,z6])],[(0,[z0,z998,z1,z4,z5,z6]),(0,[z1,z3,z825,z4,z5,z6]),(0,[z0,z32,z95,z4,z5,z6]),(0,[z0,z106,z3,z4,z5,z142]),(0,[z0,z1,z999,z4,z5,z6])],[(0,[z74,z0,z1,z3,z4,z111]),(0,[z0,z1,z3,z4,z137,z124])],[(0,[z0,z1,z3,z4,z5,z1000]),(0,[z0,z491,z293,z4,z5,z6]),(0,[z0,z1001,z3,z4,z5,z6]),(0,[z0,z1,z1002,z4,z5,z6]),(1,[z0,z764,z4,z5,z6]),(0,[z146,z74,z0,z101,z3,z4])],[(0,[z1,z3,z4,z722,z45,z6]),(0,[z0,z437,z1,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1003]),(0,[z0,z1,z3,z4,z1004,z6])]],
   [[(0,[z0,z1005,z3,z4,z5,z6]),(0,[z135,z136,z3,z4,z21,z6]),(0,[z1006,z1,z3,z4,z5,z6])],[(0,[z0,z1,z317,z9,z5,z6]),(0,[z0,z1,z577,z9,z5,z6]),(0,[z8,z1,z3,z9,z5,z75]),(0,[z146,z0,z163,z3,z4,z6])],[(0,[z0,z1007,z1,z3,z5,z6]),(0,[z117,z94,z3,z4,z5,z6]),(0,[z0,z136,z3,z9,z5,z6]),(0,[z0,z1,z1008,z3,z5,z6]),(0,[z0,z101,z3,z9,z5,z102])],[(0,[z0,z451,z3,z4,z5,z6]),(0,[z146,z0,z622,z3,z4,z6])],[(0,[z0,z1,z3,z4,z5,z1009]),(0,[z0,z381,z1,z4,z46,z6]),(0,[z0,z1,z4,z5,z6,z1010]),(0,[z0,z3,z4,z5,z6,z1011]),(0,[z0,z1,z3,z4,z5,z1012]),(0,[z256,z0,z101,z3,z4,z102]),(0,[z0,z109,z20,z1,z46,z6])],[(0,[z58,z20,z1,z62,z5,z6]),(0,[z161,z129,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z1013,z6])],[(0,[z658,z94,z3,z4,z5,z6]),(0,[z0,z136,z3,z4,z5,z168]),(0,[z0,z1,z621,z9,z5,z6]),(0,[z146,z0,z20,z3,z164,z6])],[(0,[z0,z1014,z1,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1015]),(0,[z0,z1,z9,z5,z677,z6]),(0,[z0,z1,z465,z4,z5,z6]),(0,[z0,z20,z11,z12,z5,z6]),(0,[z0,z1,z1016,z4,z5,z6])]],
   [[(0,[z0,z1,z158,z9,z5,z6]),(0,[z0,z1,z9,z5,z6,z682]),(0,[z0,z20,z1,z3,z5,z983])],[(0,[z0,z196,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z1017,z6]),(0,[z0,z3,z4,z5,z1018,z6]),(0,[z341,z1,z250,z4,z5,z6]),(0,[z1,z3,z4,z5,z748,z75]),(0,[z0,z20,z32,z33,z5,z6]),(0,[z0,z3,z9,z5,z6,z238])],[(0,[z0,z669,z1,z9,z5,z6]),(0,[z44,z1,z3,z9,z45,z6]),(0,[z0,z1,z9,z5,z687,z6]),(0,[z0,z12,z764,z4,z5,z6]),(0,[z0,z3,z4,z5,z710,z6]),(0,[z0,z1,z3,z1019,z5,z6]),(1,[z0,z860,z1,z5,z6])],[(0,[z0,z1,z1020,z4,z5,z6]),(0,[z0,z1,z3,z4,z453,z6]),(0,[z0,z7,z3,z4,z5,z204]),(0,[z0,z1,z3,z4,z1021,z6]),(0,[z0,z1,z3,z1022,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1023]),(0,[z610,z0,z20,z1,z5,z6])],[(0,[z0,z1,z352,z9,z5,z6]),(0,[z1,z3,z4,z738,z5,z6]),(0,[z0,z104,z848,z3,z5,z6]),(0,[z0,z1024,z1,z3,z5,z6]),(0,[z0,z1025,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z216,z6]),(0,[z8,z91,z3,z4,z5,z75]),(0,[z146,z0,z3,z9,z164,z6]),(0,[z0,z1,z456,z9,z5,z6]),(0,[z0,z1,z3,z1026,z5,z6])],[(0,[z0,z1,z3,z4,z1027,z6]),(0,[z0,z105,z3,z4,z5,z102]),(0,[z0,z1,z3,z70,z5,z354]),(0,[z0,z1,z438,z9,z5,z6]),(0,[z74,z0,z451,z3,z4,z6])]],
   [[(0,[z58,z196,z62,z4,z5,z6]),(0,[z0,z83,z3,z4,z5,z354]),(0,[z0,z1,z165,z9,z5,z6]),(0,[z0,z1,z3,z1028,z5,z6]),(0,[z0,z1,z3,z481,z5,z6]),(0,[z0,z1,z1029,z4,z5,z6]),(0,[z0,z536,z1,z9,z5,z6]),(0,[z0,z197,z1,z428,z5,z6])],[(0,[z193,z94,z3,z4,z5,z6]),(0,[z0,z1030,z1,z3,z5,z6]),(0,[z0,z153,z1,z14,z22,z6])],[(0,[z0,z491,z3,z4,z5,z69]),(0,[z0,z954,z3,z4,z5,z6]),(0,[z1031,z1,z3,z4,z5,z6]),(0,[z1032,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z5,z795,z241])],[(0,[z0,z1,z1033,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z204]),(0,[z256,z0,z1,z3,z4,z138]),(0,[z0,z1,z1034,z3,z5,z6]),(0,[z0,z1,z764,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1035]),(0,[z0,z170,z1,z9,z5,z80]),(0,[z0,z1036,z3,z4,z5,z6])],[(0,[z0,z1,z3,z373,z5,z6]),(0,[z118,z0,z88,z1,z5,z6]),(0,[z0,z20,z451,z3,z5,z6])],[(0,[z439,z49,z3,z4,z5,z6]),(0,[z0,z1,z3,z1037,z5,z6]),(0,[z0,z888,z1,z9,z5,z6]),(0,[z0,z1038,z3,z4,z5,z6]),(0,[z0,z1,z740,z5,z45,z6]),(0,[z0,z91,z3,z9,z5,z6]),(0,[z1039,z1,z3,z4,z5,z6]),(0,[z0,z20,z1,z3,z137,z124]),(0,[z0,z3,z4,z5,z1040,z6])],[(0,[z736,z49,z3,z4,z5,z6]),(0,[z0,z601,z1,z9,z5,z6]),(0,[z0,z1041,z3,z4,z5,z6]),(0,[z490,z129,z1,z3,z5,z6])],[(0,[z0,z1,z1042,z4,z5,z6]),(0,[z0,z694,z1,z9,z5,z6]),(0,[z0,z1043,z1,z3,z5,z6]),(0,[z0,z1,z300,z5,z46,z6])]],
   [[(0,[z0,z491,z103,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z748]),(0,[z0,z3,z4,z710,z164,z6]),(0,[z1,z3,z4,z5,z909,z6])],[(0,[z0,z1,z1044,z3,z4,z5]),(0,[z0,z11,z32,z9,z5,z6]),(0,[z108,z0,z1,z3,z5,z360]),(0,[z0,z109,z1,z4,z818,z6])],[(0,[z249,z1,z250,z4,z5,z6]),(0,[z0,z1,z9,z5,z59,z6]),(0,[z0,z1,z718,z3,z5,z6]),(0,[z0,z1,z3,z1045,z5,z6])],[(0,[z0,z1,z187,z9,z5,z6]),(0,[z8,z1,z3,z4,z5,z748]),(0,[z839,z1,z3,z9,z5,z6]),(0,[z0,z1046,z3,z4,z5,z6]),(0,[z0,z1,z4,z818,z46,z6])],[(0,[z0,z1,z1047,z4,z5,z6]),(0,[z0,z1048,z3,z4,z5,z6]),(0,[z441,z0,z1,z9,z5,z6]),(0,[z0,z527,z1,z9,z5,z6]),(0,[z0,z1,z1049,z3,z5,z6]),(0,[z0,z1,z121,z9,z5,z6]),(0,[z0,z1,z585,z9,z5,z6]),(0,[z0,z1,z3,z1050,z5,z6]),(0,[z0,z1,z3,z1051,z5,z6])],[(0,[z0,z302,z1,z1047,z5,z6]),(0,[z0,z307,z1,z9,z5,z6]),(0,[z0,z1,z1052,z4,z5,z6]),(0,[z0,z1,z3,z1053,z5,z6]),(0,[z0,z515,z1,z9,z5,z6]),(0,[z118,z0,z20,z1,z5,z6])],[(0,[z0,z101,z3,z4,z331,z102]),(0,[z256,z0,z106,z1,z3,z4])],[(0,[z0,z1,z3,z4,z1054,z6]),(0,[z0,z1,z3,z1055,z5,z6]),(0,[z0,z1,z3,z4,z5,z1056]),(0,[z0,z1,z9,z5,z303,z6]),(0,[z0,z340,z1,z3,z22,z6])]],
   [[(0,[z0,z888,z1,z3,z5,z6]),(0,[z0,z1,z740,z4,z5,z6]),(0,[z0,z437,z1,z116,z5,z6]),(0,[z0,z1057,z1,z3,z5,z6]),(0,[z146,z0,z163,z3,z4,z5]),(0,[z0,z1,z14,z4,z5,z6])],[(0,[z0,z94,z3,z4,z5,z16]),(0,[z0,z20,z843,z3,z5,z6]),(0,[z0,z1,z121,z140,z5,z81]),(0,[z0,z40,z1,z330,z5,z80])],[(0,[z249,z324,z1,z250,z5,z6]),(0,[z0,z1058,z1,z3,z5,z6]),(0,[z0,z12,z4,z5,z79,z6]),(0,[z0,z3,z4,z31,z6,z444]),(0,[z0,z1,z575,z9,z5,z6]),(0,[z0,z1059,z3,z4,z5,z6]),(0,[z0,z1,z1060,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1061]),(0,[z0,z20,z1,z3,z453,z6])],[(0,[z0,z196,z3,z4,z172,z6]),(0,[z0,z1,z3,z1062,z5,z6]),(0,[z0,z957,z3,z9,z5,z6])],[(0,[z1063,z0,z1,z3,z4,z6]),(0,[z0,z912,z3,z4,z5,z6]),(0,[z0,z440,z1,z293,z5,z6]),(0,[z0,z1064,z3,z4,z5,z6]),(0,[z0,z20,z3,z5,z61,z6])],[(0,[z0,z1,z3,z1065,z5,z6]),(0,[z0,z1,z3,z4,z5,z1066]),(0,[z0,z20,z1,z3,z216,z6]),(0,[z0,z1,z524,z9,z5,z6]),(0,[z0,z1,z3,z4,z5,z798])],[(0,[z0,z571,z3,z4,z5,z102]),(0,[z0,z20,z1,z3,z5,z354]),(0,[z540,z1,z62,z4,z5,z6]),(0,[z1,z3,z130,z738,z5,z6]),(0,[z166,z1,z3,z4,z5,z138]),(0,[z0,z163,z30,z1,z3,z4]),(0,[z0,z1,z121,z3,z5,z6])]],
   [[(0,[z0,z1,z425,z9,z5,z6])],[(0,[z141,z94,z3,z9,z5,z6]),(1,[z1,z825,z4,z5,z6]),(0,[z249,z1,z825,z4,z5,z6]),(0,[z0,z1,z1067,z3,z5,z6]),(0,[z0,z153,z1,z293,z5,z6]),(0,[z0,z32,z9,z33,z5,z6]),(0,[z0,z1,z9,z5,z132,z6])],[(0,[z146,z0,z3,z4,z308,z6]),(0,[z0,z1068,z3,z4,z5,z6]),(0,[z0,z1,z1069,z4,z5,z6]),(0,[z0,z1,z569,z9,z5,z6])],[(0,[z0,z1070,z3,z4,z5,z6]),(0,[z540,z1,z3,z19,z5,z6]),(0,[z0,z1,z3,z1071,z5,z6]),(0,[z0,z20,z1,z3,z5,z204]),(0,[z0,z1,z9,z5,z80,z138]),(0,[z0,z1,z3,z4,z5,z1072]),(0,[z0,z1,z3,z1073,z5,z6]),(0,[z1074,z1,z3,z4,z5,z6]),(0,[z0,z662,z1,z9,z5,z6]),(0,[z0,z101,z3,z4,z550,z5]),(0,[z0,z1,z13,z9,z5,z6]),(0,[z1075,z1,z3,z4,z5,z6])],[(1,[z736,z3,z4,z5,z6]),(0,[z0,z1,z572,z9,z5,z6]),(0,[z0,z1,z9,z5,z6,z328])],[(0,[z0,z1,z3,z1076,z5,z6]),(0,[z0,z1,z3,z4,z1077,z6]),(0,[z0,z290,z3,z4,z5,z102])],[(0,[z496,z1,z3,z4,z45,z6]),(0,[z0,z1,z3,z9,z981,z6]),(0,[z0,z1,z4,z5,z80,z813]),(0,[z1078,z1,z3,z4,z5,z6])],[(0,[z466,z1,z3,z4,z5,z75]),(0,[z0,z480,z1,z9,z5,z6])]],
   [[],[(0,[z0,z1,z3,z4,z5,z1079]),(0,[z0,z1,z355,z9,z5,z6]),(0,[z0,z20,z1,z465,z5,z6])],[(0,[z0,z1080,z3,z4,z5,z6]),(0,[z0,z1081,z1,z4,z5,z6]),(0,[z0,z791,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z956,z6])],[(0,[z0,z1,z3,z4,z5,z1082]),(0,[z0,z1,z3,z4,z5,z1083]),(0,[z1,z250,z825,z4,z5,z6]),(0,[z0,z1,z617,z9,z5,z6])],[(0,[z0,z1,z3,z1084,z5,z6]),(0,[z0,z1,z361,z9,z5,z6]),(0,[z0,z20,z91,z3,z5,z6]),(0,[z0,z20,z1,z3,z5,z93])],[(0,[z0,z1085,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z17]),(0,[z0,z1,z1086,z4,z5,z6]),(0,[z0,z1,z3,z5,z1087,z6]),(0,[z0,z302,z1,z3,z22,z6]),(0,[z0,z88,z1,z9,z5,z6]),(0,[z0,z20,z785,z3,z5,z6]),(0,[z0,z588,z1,z14,z5,z6])],[(0,[z0,z1,z3,z4,z1088,z6]),(0,[z0,z1,z3,z4,z5,z1089]),(0,[z118,z0,z1,z121,z5,z6])],[(0,[z0,z7,z3,z4,z5,z6]),(0,[z0,z11,z1,z481,z5,z6]),(0,[z0,z848,z3,z35,z5,z6]),(0,[z0,z1,z3,z4,z124,z299]),(0,[z0,z30,z3,z9,z31,z6]),(0,[z0,z30,z3,z4,z6,z685])]],
   [[(0,[z0,z1,z1090,z4,z5,z6]),(0,[z0,z1091,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1092]),(0,[z0,z1,z3,z1093,z5,z6]),(1,[z0,z1,z740,z5,z6]),(0,[z0,z1,z9,z21,z46,z6]),(0,[z0,z1,z9,z5,z360,z6]),(0,[z0,z1,z140,z4,z5,z319])],[(0,[z0,z1094,z1,z3,z5,z6]),(0,[z0,z1,z293,z4,z453,z6]),(0,[z0,z1,z314,z9,z5,z6]),(0,[z0,z1,z85,z3,z5,z241]),(0,[z0,z1,z3,z1095,z5,z6]),(0,[z146,z0,z163,z1,z3,z4]),(0,[z0,z340,z1,z9,z46,z6]),(0,[z0,z1,z614,z9,z5,z6])],[(0,[z0,z1,z3,z233,z5,z354]),(0,[z0,z921,z3,z4,z5,z6])],[(0,[z0,z40,z1,z41,z5,z80])],[(0,[z326,z49,z3,z4,z5,z6]),(0,[z0,z1,z3,z1096,z5,z6]),(0,[z58,z1,z62,z4,z5,z17]),(0,[z0,z71,z3,z4,z453,z6]),(0,[z0,z1,z293,z4,z216,z6]),(0,[z0,z1,z3,z4,z453,z245]),(0,[z0,z1,z3,z1097,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1098]),(0,[z0,z1,z428,z9,z5,z6])],[(0,[z0,z1099,z3,z4,z5,z6]),(0,[z146,z0,z3,z4,z519,z6]),(0,[z221,z1,z3,z36,z5,z6]),(0,[z0,z1,z173,z3,z9,z5])],[(0,[z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z16]),(0,[z0,z1,z3,z4,z5,z1100]),(0,[z0,z1,z3,z1101,z5,z6]),(0,[z0,z71,z3,z4,z216,z6]),(0,[z0,z1,z3,z4,z216,z245]),(0,[z166,z20,z1,z3,z5,z138]),(0,[z0,z11,z223,z4,z5,z6]),(0,[z0,z106,z3,z9,z5,z142]),(0,[z0,z605,z1,z9,z5,z6]),(0,[z0,z1,z9,z5,z208,z6])]],
   [[(0,[z0,z1102,z1,z3,z5,z6]),(0,[z0,z32,z1,z9,z5,z6]),(0,[z118,z0,z1,z116,z5,z6]),(0,[z1103,z1,z3,z4,z5,z6]),(0,[z0,z88,z1,z3,z5,z6]),(0,[z0,z242,z1,z9,z5,z6]),(0,[z74,z0,z1,z140,z9,z5]),(0,[z0,z1,z3,z9,z137,z124]),(0,[z1104,z0,z1,z3,z5,z6])],[(0,[z0,z1,z3,z1105,z5,z6]),(0,[z0,z1,z3,z4,z1106,z6]),(0,[z0,z1107,z1,z3,z5,z6]),(0,[z0,z1,z87,z3,z5,z119])],[(0,[z0,z196,z3,z4,z5,z17]),(0,[z0,z1,z3,z1108,z5,z6]),(0,[z0,z437,z1,z9,z5,z6]),(0,[z0,z3,z4,z5,z142,z472])],[(0,[z0,z1,z1109,z3,z5,z6]),(0,[z369,z1,z3,z4,z21,z6]),(0,[z0,z1,z475,z9,z5,z6]),(0,[z540,z1,z3,z143,z5,z6]),(0,[z0,z1,z782,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z913]),(0,[z0,z20,z1,z3,z5,z1072])],[(0,[z0,z669,z4,z33,z5,z6]),(0,[z0,z491,z3,z4,z5,z245]),(0,[z0,z1,z3,z4,z137,z421]),(0,[z256,z0,z3,z4,z142,z6]),(0,[z0,z1,z3,z1110,z5,z6])],[(0,[z0,z565,z1,z9,z5,z6]),(0,[z0,z20,z1,z3,z1077,z6])],[(0,[z58,z1,z62,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1111]),(0,[z0,z1,z1112,z4,z5,z6]),(0,[z0,z451,z3,z9,z5,z6])],[(0,[z0,z1,z3,z4,z1113,z6]),(0,[z0,z175,z3,z4,z5,z138]),(0,[z386,z1,z3,z4,z5,z138]),(0,[z74,z0,z451,z1,z3,z4])]],
   [[(0,[z0,z1,z162,z9,z5,z6]),(0,[z0,z11,z12,z481,z5,z6]),(0,[z0,z1114,z1,z3,z5,z6]),(0,[z0,z1,z236,z4,z5,z6]),(0,[z0,z1,z3,z9,z1013,z6])],[(0,[z0,z1,z644,z9,z5,z6]),(0,[z0,z1115,z1,z4,z5,z6]),(0,[z0,z109,z1,z4,z46,z6])],[(0,[z0,z1,z3,z1116,z5,z6]),(0,[z0,z1,z3,z4,z5,z1117]),(0,[z0,z11,z764,z4,z5,z6]),(0,[z0,z1,z465,z9,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1118]),(0,[z0,z1,z1119,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1120]),(0,[z44,z1,z3,z289,z45,z6]),(0,[z0,z1,z255,z9,z5,z6]),(0,[z0,z104,z3,z35,z5,z6]),(0,[z0,z1,z652,z9,z5,z6]),(0,[z0,z1121,z3,z4,z5,z6])],[(0,[z0,z196,z3,z9,z5,z6]),(0,[z0,z196,z3,z70,z5,z6]),(0,[z0,z440,z1,z9,z5,z6]),(0,[z0,z20,z1,z9,z5,z6]),(0,[z1122,z1,z3,z4,z5,z6])],[(0,[z0,z1123,z1,z3,z4,z5]),(0,[z0,z20,z1,z3,z5,z17]),(0,[z0,z1,z9,z5,z414,z6]),(0,[z0,z1,z3,z4,z453,z69]),(0,[z0,z1,z442,z9,z5,z6])],[(0,[z0,z1,z3,z9,z453,z6]),(0,[z0,z1,z656,z9,z5,z6]),(0,[z0,z252,z3,z4,z5,z93])],[(0,[z0,z1124,z1,z3,z5,z6]),(0,[z44,z302,z1,z3,z45,z6]),(0,[z122,z1,z3,z4,z5,z138])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 519) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 519).take 529) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1048).take 161) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1209)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [519, 529, 161] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 107).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 107).take 107).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 214).take 42).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [107, 107, 42] = true :=
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

end PEqualNP.Outside.L_meta_43892

theorem PEqualNP.Outside.L_meta_43892 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4276799616) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4276799616) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_43892.solve