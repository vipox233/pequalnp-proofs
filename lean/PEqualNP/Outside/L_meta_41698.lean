import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_41698

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
  Nat.testBit (4276676840 * 2 ^ 32 + 3938511040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x400c6c51b15e0de0#64 ++ 0x08018d8a362bc1bc#64 ++ 0xe01cfcf3f3fe1fe5#64 ++ 0xfc039f9e7e7fc3fc#64 : BitVec 256),
   (0x00e1152454c2a2a8#64 ++ 0x001c22a48a985455#64 ++ 0xe1e31f3c7cc7e3fe#64 ++ 0xfc3c63e78f98fc7f#64 : BitVec 256),
   (0x2e02a28a8b055450#64 ++ 0x45c054515160aa8a#64 ++ 0xfe03e3cf8f07fc7f#64 ++ 0x7fc07c79f1e0ff8f#64 : BitVec 256),
   (0x977403f00ea87b00#64 ++ 0x92ee807e01d50f60#64 ++ 0xdffc03f00ff87f87#64 ++ 0xdbff807e01ff0ff0#64 : BitVec 256),
   (0x1bbbfc000ff78001#64 ++ 0x23777f8001fef000#64 ++ 0x1ffffc000fff8007#64 ++ 0xe3ffff8001fff000#64 : BitVec 256),
   (0xbddfdbff60000002#64 ++ 0x37bbfb7fec000000#64 ++ 0xbffffffff0000007#64 ++ 0xb7fffffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 3]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [8, 5]⟩, ⟨.or, [6, 10]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [9, 12]⟩, ⟨.and, [11, 13]⟩, ⟨.or, [7, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x00400124500022a8 0x000800248a000455 0xe000033c700063f8 0x1c0000678e000c7f

def z1 : W := mkw 0x1b1ae8000b350001 0x23635d000166a000 0x1e1ce00003380001 0x03c39c0000670000

def z2 : W := mkw 0x2e02a28a8b055450 0x45c054515160aa8a 0xfe03e3cf8f07fc7f 0x7fc07c79f1e0ff8f

def z3 : W := mkw 0x400c6c51b15e0de0 0x08018d8a362bc1bc 0xe01cfcf3f3fe1fe5 0xfc039f9e7e7fc3fc

def z4 : W := mkw 0x977403f00ea87b00 0x92ee807e01d50f60 0xdffc03f00ff87f87 0xdbff807e01ff0ff0

def z5 : W := mkw 0xbddfdbff60000002 0x37bbfb7fec000000 0xbffffffff0000007 0xb7fffffffe000000

def z6 : W := mkw 0x00e1152454c2a2a8 0x001c22a48a985455 0xe1e31f3c7cc7e3fe 0xfc3c63e78f98fc7f

def z7 : W := mkw 0x19fbdd2454c2a2a8 0x233f7ba48a985455 0xffffff3c7cc7e3ff 0xffffffe78f98fc7f

def z8 : W := mkw 0x1bbbfc000ff78001 0x23777f8001fef000 0x1ffffc000fff8007 0xe3ffff8001fff000

def z9 : W := mkw 0x400c6851a11c0d40 0x08018d0a342381a8 0xe01ce0c3833e1c65 0x7c039c187067c38c

def z10 : W := mkw 0xbd1ecadb20000002 0x37a3d95b64000000 0xbe1cfcf3f0000005 0xb7c39f9e7e000000

def z11 : W := mkw 0x00086c0001560000 0x00010d80002ac000 0x001cfc0003fe0005 0xe0039f80007fc000

def z12 : W := mkw 0x844403f000087b00 0x9088807e00010f60 0xc00003f000007f80 0x1800007e00000ff0

def z13 : W := mkw 0xb77403ff6ea87b02 0x96ee807fedd50f60 0xfffc03fffff87f87 0xdfff807fffff0ff0

def z14 : W := mkw 0x133000000ea87b00 0x8266000001d50f60 0x5ffc00000ff87f87 0xcbff800001ff0ff0

def z15 : W := mkw 0xa44403ff60000002 0x1488807fec000000 0xa00003fff0000000 0x1400007ffe000000

def z16 : W := mkw 0x40086c01b15604e0 0x08010d80362ac09c 0x2000fc03f0060060 0x24001f807e00c00c

def z17 : W := mkw 0x977003a00ea07200 0x92ee007401d40e40 0x1fe003000c006002 0x03fc006001800c00

def z18 : W := mkw 0x1bbbfc000ffffb01 0xa3777f8001ffff60 0x5ffffc000fffff87 0xebffff8001fffff0

def z19 : W := mkw 0x422c6c51bffe7fe0 0x88458d8a37ffcffc 0xe01cfcf3fffe7fe5 0xfc039f9e7fffcffc

def z20 : W := mkw 0x0020040004c28000 0x0004008000985000 0x000000000cc78000 0x400000000198f000

def z21 : W := mkw 0xbddfdbff60087b02 0xb7bbfb7fec010f60 0xfffffffff0007f87 0xbffffffffe000ff0

def z22 : W := mkw 0x00a1140004c28000 0x0014228000985000 0x01e31c000cc78006 0xe03c63800198f000

def z23 : W := mkw 0x133000000ea00000 0x0266000001d40000 0x1ffc00000ff80007 0xc3ff800001ff0000

def z24 : W := mkw 0x937401700ea82b00 0x926e802e01d50560 0x1ffc00300ff80387 0xc3ff800601ff0070

def z25 : W := mkw 0x000c485120000000 0x0001890a24000000 0xa01cfcf3f0000005 0xb4039f9e7e000000

def z26 : W := mkw 0xfddffffff15e0de2 0x3fbbfffffe2bc1bc 0xfffffffff3fe1fe7 0xfffffffffe7fc3fc

def z27 : W := mkw 0x40040051b0080de0 0x0800800a360101bc 0xe00000f3f0001fe0 0x1c00001e7e0003fc

def z28 : W := mkw 0x400c4c51305a09a0 0x0801898a260b4134 0xa01cfcf3f0f80385 0xb4039f9e7e1f0070

def z29 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z30 : W := mkw 0x00e1152454c2a2a8 0x001c22a48a985455 0x01e01c3070c00380 0x803c03860e180070

def z31 : W := mkw 0x2ee3b7aedfc7f6f8 0x45dc76f5dbf8fedf 0xffe3ffffffc7ffff 0xfffc7ffffff8ffff

def z32 : W := mkw 0x00000400104200a0 0x0000008002084014 0xe0001c3070c603e4 0xfc0003860e18c07c

def z33 : W := mkw 0x1bbbf8000fb58001 0x23777f0001f6b000 0x1fffe0000f398003 0x03fffc0001e73000

def z34 : W := mkw 0x40ed7d75f5deafe8 0x081dafaebebbd5fd 0xe1ffffffffffffff 0xfc3fffffffffffff

def z35 : W := mkw 0x0020040014c2a2a8 0x0004008002985455 0x400000000cc7e3f8 0x480000000198fc7f

def z36 : W := mkw 0xbd1ecadb20000002 0x37a3d95b64000000 0x1e1ce0c380000001 0x03c39c1870000000

def z37 : W := mkw 0x288bd80f60000002 0x25117b01ec000000 0x2003fc0ff0000000 0x24007f81fe000000

def z38 : W := mkw 0x40002400915e0de0 0x08000480122bc1bc 0x4000000003fe1fe0 0x48000000007fc3fc

def z39 : W := mkw 0xbdd393ae40000002 0x37ba7275c8000000 0x1fe3030c00000002 0x03fc606180000000

def z40 : W := mkw 0xbff393ae4ea07202 0xb7fe7275c9d40e40 0x1fe3030c0c006002 0x03fc606181800c00

def z41 : W := mkw 0x00c115245042a2a8 0x001822a48a085455 0xe0031f3c7007e3f8 0x3c0063e78e00fc7f

def z42 : W := mkw 0x2e02828a0a015010 0x45c0505141402a02 0x1e03030c0c01e01a 0x03c0606181803c03

def z43 : W := mkw 0x3ffbffaedff7f6f9 0x67ff7ff5dbfefedf 0xffffffffffffffff 0xffffffffffffffff

def z44 : W := mkw 0x060002800a005000 0x00c0005001400a00 0xfe0303cc0f07fc7f 0x7fc0607981e0ff8f

def z45 : W := mkw 0x00a1100004808000 0x0014220000901000 0x01e300000c018002 0x003c600001803000

def z46 : W := mkw 0xbddfffff61578003 0x37bbffffec2af000 0xbffffffff0078007 0xb7fffffffe00f000

def z47 : W := mkw 0x977403f00ea87b00 0x92ee807e01d50f60 0x1ffc03300cf86382 0x83ff8066019f0c70

def z48 : W := mkw 0x060402d00a085900 0x00c0805a01410b20 0xde1c03f00ff87f87 0xdbc3807e01ff0ff0

def z49 : W := mkw 0x060002800a005000 0x00c0005001400a00 0xde0003c00f007c07 0x5bc0007801e00f80

def z50 : W := mkw 0x2802a00a81050450 0x450054015020a08a 0x2003e00f80078078 0x24007c01f000f00f

def z51 : W := mkw 0x288fd85f60000002 0x2511fb0bec000000 0xa01ffcfff0000005 0xb403ff9ffe000000

def z52 : W := mkw 0x9114005000280900 0x9222800a00050120 0x001c000000380000 0x0003800000070000

def z53 : W := mkw 0x422024009fff8de1 0x0844048013fff1bc 0x400000000fff9fe0 0x4800000001fff3fc

def z54 : W := mkw 0x1bb390000ea18001 0x2376720001d43000 0x1fe300000c018002 0x03fc600001803000

def z55 : W := mkw 0x0060052454c2a2a8 0x000c00a48a985455 0xe000033c7cc7e3f8 0x5c0000678f98fc7f

def z56 : W := mkw 0x9174017004a82b00 0x922e802e00950560 0x01fc003000f80380 0x803f8006001f0070

def z57 : W := mkw 0xbffbffae4ff78003 0x37ff7ff5c9fef000 0x1fffff0c0fff8007 0xe3ffffe181fff000

def z58 : W := mkw 0x288bfc0f61578003 0x25117f81ec2af000 0x2003fc0ff0078000 0x24007f81fe00f000

def z59 : W := mkw 0x00811404504280a8 0x001022808a085015 0x20031c0c70078078 0x240063818e00f00f

def z60 : W := mkw 0x971402d00a285900 0x92e2805a01450b20 0x1e1c00c003381c01 0x03c3801800670380

def z61 : W := mkw 0x02e135245ff7a2a9 0x005c26a48bfef455 0xe1e31f3c7fffe3fe 0xfc3c63e78ffffc7f

def z62 : W := mkw 0x13386c000ff60000 0x02670d8001fec000 0x1ffcfc000ffe0007 0xe3ff9f8001ffc000

def z63 : W := mkw 0x400c6c51a15e0d40 0x08018d8a342bc1a8 0x001cfcc383fe1c05 0xe0039f98707fc380

def z64 : W := mkw 0x11b95c0004f28001 0x22372b80009e5000 0x01ff1c000cff8006 0xe03fe380019ff000

def z65 : W := mkw 0x0064017004882b00 0x000c802e00910560 0xc1fc03f00ff87f87 0xd83f807e01ff0ff0

def z66 : W := mkw 0x420c6c51bb5f5df0 0x48418d8a376bebbe 0xe01cfcf3fffffffd 0xfc039f9e7fffffff

def z67 : W := mkw 0x2e02828a0a015010 0x45c0505141402a02 0x1e00000000000000 0x03c0000000000000

def z68 : W := mkw 0x0004005000080900 0x0000800a00010120 0xc01c00f003f81f85 0xd803801e007f03f0

def z69 : W := mkw 0x1b32a0000fa50000 0x0366540001f4a000 0x1fffe0000fff8007 0xe3fffc0001fff000

def z70 : W := mkw 0xbfffdbff6ea87b02 0xb7fffb7fedd50f60 0xfffffffffff87f87 0xffffffffffff0ff0

def z71 : W := mkw 0x199bfc0001578001 0x23337f80002af000 0x1ffffc0000078007 0xa3ffff800000f000

def z72 : W := mkw 0x977407f01eea7ba0 0x92ee80fe03dd4f74 0xfffc1ff07ffe7fe7 0xffff83fe0fffcffc

def z73 : W := mkw 0x460c6ed1bb5e5de0 0x08c18dda376bcbbc 0xfe1cfff3fffe7fe7 0xffc39ffe7fffcffc

def z74 : W := mkw 0x0000000000000000 0x0000000000000000 0x0003030c0c01e01a 0x0000606181803c03

def z75 : W := mkw 0x0060012004802200 0x000c002400900440 0xc1e003300cc06386 0xd83c006601980c70

def z76 : W := mkw 0x00e111245480a2a8 0x001c22248a901455 0xe1e3033c7c01e3fa 0x1c3c60678f803c7f

def z77 : W := mkw 0x00a1140454c2a2a8 0x001422808a985455 0x60031c0c7cc7e3f8 0x6c0063818f98fc7f

def z78 : W := mkw 0x00c1112440000000 0x0018222488000000 0xa1e31f3c70000006 0xb43c63e78e000000

def z79 : W := mkw 0xa44003ae40000002 0x14880075c8000000 0x0000030c00000000 0x0000006180000000

def z80 : W := mkw 0x5bbbfc009fff8de1 0x2b777f8013fff1bc 0x5ffffc000fff9fe7 0xebffff8001fff3fc

def z81 : W := mkw 0x2e02a28a8b055450 0x45c054515160aa8a 0xfe00e0c383061c65 0x7fc01c187060c38c

def z82 : W := mkw 0x0081100440008008 0x0010220088001001 0x0003000c00018018 0x0000600180003003

def z83 : W := mkw 0x11b95c0004f28001 0x22372b80009e5000 0x01fc1c0000f80000 0x803f8380001f0000

def z84 : W := mkw 0x864403f00a087b00 0x90c8807e01410f60 0xde0003f00f007f87 0x5bc0007e01e00ff0

def z85 : W := mkw 0x2400028a80005450 0x4480005150000a8a 0xe00003cf80007c78 0x1c000079f0000f8f

def z86 : W := mkw 0x2400028a00000000 0x0480005140000000 0xa00003cf80000000 0x14000079f0000000

def z87 : W := mkw 0x020020008b055450 0x404004001160aa8a 0x400000000f07fc78 0x4800000001e0ff8f

def z88 : W := mkw 0xbfdffbffeb055452 0x77fbff7ffd60aa8a 0xffffffffff07fc7f 0xffffffffffe0ff8f

def z89 : W := mkw 0x40e97d25f5d6a6e8 0x081d2fa4bebad4dd 0xe1e3ff3ffcc7e3fe 0xfc3c7fe7ff98fc7f

def z90 : W := mkw 0xbf72a3aa8fa57650 0xd7ee547551f4aeca 0xffe3e3cf8f07fc7f 0x7ffc7c79f1e0ff8f

def z91 : W := mkw 0x000c485120080900 0x0001890a24010120 0xe01cfcf3f3f81f85 0xfc039f9e7e7f03f0

def z92 : W := mkw 0x022000000ea87b00 0x8044000001d50f60 0x400000000ff87f80 0x4800000001ff0ff0

def z93 : W := mkw 0x00000400104200a0 0x0000008002084014 0x20001c0070060060 0x240003800e00c00c

def z94 : W := mkw 0x00e1152454c2a2a8 0x001c22a48a985455 0x21e31c3c70c783f8 0xa43c63878e18f07f

def z95 : W := mkw 0x1bbffc512ff78001 0x2377ff8a25fef000 0xbffffcf3ffff8007 0xf7ffff9e7ffff000

def z96 : W := mkw 0x1bfbfd245ff7a2a9 0x237f7fa48bfef455 0x1ffffc307fff8387 0xe3ffff860ffff070

def z97 : W := mkw 0x400c4c51b05a0de0 0x0801898a360b41bc 0xe01c1cf3f0f81fe0 0x9c03839e7e1f03fc

def z98 : W := mkw 0x844003a000007200 0x9088007400000e40 0x0000030000006000 0x0000006000000c00

def z99 : W := mkw 0x97fd5bf56ea87b02 0xb2ffab7eadd50f60 0xdffc1ff07ff87f87 0xdbff83fe0fff0ff0

def z100 : W := mkw 0x97f517f45eeafba8 0x92fea2fe8bdd5f75 0xdffc1ff07ff87f87 0xdbff83fe0fff0ff0

def z101 : W := mkw 0x08abfc0005d78001 0x21157f8000baf000 0x01e3fc000cc78006 0xe03c7f800198f000

def z102 : W := mkw 0x0000000000000000 0x0000000000000000 0x001c000003f80005 0xc0038000007f0000

def z103 : W := mkw 0x6e0eeedbbb5f5df0 0x4dc1dddb776bebbe 0xfe1fffffffffffff 0xffc3ffffffffffff

def z104 : W := mkw 0xe44403fff0080de2 0x1c88807ffe0101bc 0xe00003fff0001fe0 0x1c00007ffe0003fc

def z105 : W := mkw 0x91f5157454eaaba8 0x923ea2ae8a9d5575 0xe1ff1f3c7cffe3fe 0xfc3fe3e78f9ffc7f

def z106 : W := mkw 0x00c1112440000000 0x0018222488000000 0xe1e31f3c7c07e07e 0xfc3c63e78f80fc0f

def z107 : W := mkw 0x955403f000000000 0x12aa807e00000000 0x9ffc03f000000007 0x93ff807e00000000

def z108 : W := mkw 0x02286c000ff78001 0x00450d8001fef000 0x001cfc000fff8005 0xe0039f8001fff000

def z109 : W := mkw 0x020000000a015010 0x4040000001402a02 0x000000000c01e018 0x0000000001803c03

def z110 : W := mkw 0x133024000ff78001 0x0266048001fef000 0x1ffc00000fff8007 0xc3ff800001fff000

def z111 : W := mkw 0x1118480000300001 0x2223090000060000 0x001c000000380000 0x0003800000070000

def z112 : W := mkw 0x088bfc0001578001 0x21117f80002af000 0x0003fc0000078000 0x20007f800000f000

def z113 : W := mkw 0x400c4c51305a09a0 0x0801898a260b4134 0x001c1c3070f80380 0x800383860e1f0070

def z114 : W := mkw 0x2e02a28a0b050000 0x05c054514160a000 0xbe03e3cf8f078007 0x77c07c79f1e0f000

def z115 : W := mkw 0xa44403fa80087f50 0xd488807f50010fea 0xe00003ff80007ff8 0x1c00007ff0000fff

def z116 : W := mkw 0xbf76a3fa8fad7f50 0xd7eed47f51f5afea 0xffffe3ff8fffffff 0xfffffc7ff1ffffff

def z117 : W := mkw 0x1bb390000ea18001 0x2376720001d43000 0x1fff00000ff98007 0xc3ffe00001ff3000

def z118 : W := mkw 0x000c4c51304200a0 0x0001898a26084014 0xe01cfcf3f0c603e5 0xfc039f9e7e18c07c

def z119 : W := mkw 0x2e02a28a8b055450 0x45c054515160aa8a 0xbe03e3cf83001c07 0x37c07c79f0600380

def z120 : W := mkw 0xbdffdfff74c2a2aa 0x37bffbffee985455 0xfffffffffcc7e3ff 0xffffffffff98fc7f

def z121 : W := mkw 0x977427f00ffffb01 0x92ee84fe01ffff60 0xdffc03f00fffff87 0xdbff807e01fffff0

def z122 : W := mkw 0x2400028a80005450 0x4480005150000a8a 0x000000c380001c00 0x0000001870000380

def z123 : W := mkw 0x022024001ff7a2a9 0x0044048003fef455 0x400000000fffe3f8 0x4800000001fffc7f

def z124 : W := mkw 0x9fbffed00fffd901 0xb3f7ffda01fffb20 0x1ffffcc00fff9c07 0xe3ffff9801fff380

def z125 : W := mkw 0x91dd597560000002 0x323bab2eac000000 0x01fc1c3070000000 0x803f83860e000000

def z126 : W := mkw 0x022000000ea07200 0x8044000001d40e40 0x000000000c006000 0x0000000001800c00

def z127 : W := mkw 0x5b1eec51bb7f0de1 0x2b63dd8a376fe1bc 0xfe1cfcf3f3fe1fe5 0xffc39f9e7e7fc3fc

def z128 : W := mkw 0xbdd393ae40000002 0x37ba7275c8000000 0xbfe31f3c70000006 0xb7fc63e78e000000

def z129 : W := mkw 0xbfffffff6ff78003 0x37ffffffedfef000 0xbfffffffffff8007 0xf7fffffffffff000

def z130 : W := mkw 0xbff393ae4ea18003 0x37fe7275c9d43000 0x1fe3030c0c018002 0x03fc606181803000

def z131 : W := mkw 0x2c02828a00000000 0x0580505140000000 0xbe03e3cf80000007 0x37c07c79f0000000

def z132 : W := mkw 0x0000000000000000 0x0000000000000000 0xe003030c0c07e07e 0x7c0060618180fc0f

def z133 : W := mkw 0x1bbbfc000ff78001 0x23777f8001fef000 0xffffff0c0fffe07f 0xffffffe181fffc0f

def z134 : W := mkw 0xbddfdbffe0005452 0x77bbfb7ffc000a8a 0xfffffffff0007c7f 0xbffffffffe000f8f

def z135 : W := mkw 0x5bbffc51bfff8de1 0x2b77ff8a37fff1bc 0xfffffcf3ffff9fe7 0xffffff9e7ffff3fc

def z136 : W := mkw 0x0004005120000000 0x0000800a24000000 0xa00000f3f0000000 0x1400001e7e000000

def z137 : W := mkw 0xbddffbffe1040442 0x37bbff7ffc208088 0xfffffffff3061c67 0xfffffffffe60c38c

def z138 : W := mkw 0x1b9bf8000b050000 0x23737f000160a000 0x1ffffc000f078007 0xe3ffff8001e0f000

def z139 : W := mkw 0x488bfc01b15784e1 0x29117f80362af09c 0x2003fc03f0078060 0x24007f807e00f00c

def z140 : W := mkw 0x533c6c51bffe0de0 0x0a678d8a37ffc1bc 0xfffcfcf3fffe1fe7 0xffff9f9e7fffc3fc

def z141 : W := mkw 0x0a02a0000b050000 0x014054000160a000 0xfe03e30c0f07e07f 0x7fc07c6181e0fc0f

def z142 : W := mkw 0x020000000a000000 0x0040000001400000 0x1e0000000f000007 0x43c0000001e00000

def z143 : W := mkw 0xbffffbffefad7f52 0xf7ffff7ffdf5afea 0xffffffffffffffff 0xffffffffffffffff

def z144 : W := mkw 0x0020040014c2a2a8 0x0004008002985455 0xe003030c0cc7e3fe 0x7c0060618198fc7f

def z145 : W := mkw 0x080ae80001150001 0x21015d000022a000 0x0000e00000000000 0x00001c0000000000

def z146 : W := mkw 0x1bbbfc000ff78001 0x23777f8001fef000 0x1ffcfc0003f80001 0x83ff9f80007f0000

def z147 : W := mkw 0x6e0eeadbab1d5d50 0x4dc1dd5b7563abaa 0xfe1fe3cf8f3ffc7f 0x7fc3fc79f1e7ff8f

def z148 : W := mkw 0xc44c6ff1b15e7fe0 0x98898dfe362bcffc 0xe01cfff3f3fe7fe5 0xfc039ffe7e7fcffc

def z149 : W := mkw 0xbdd393ae40000002 0x37ba7275c8000000 0xbfe3e3cf80000007 0x37fc7c79f0000000

def z150 : W := mkw 0x955c4bf120000000 0x12ab897e24000000 0xbffcfff3f0000007 0xb7ff9ffe7e000000

def z151 : W := mkw 0x2e02a28a8b055450 0x45c054515160aa8a 0x1e03e0c38f079c07 0x63c07c1871e0f380

def z152 : W := mkw 0x40042051b10c0de0 0x0800840a362181bc 0xe000e0f3f3061fe5 0x7c001c1e7e60c3fc

def z153 : W := mkw 0x13b97c000ff78001 0x22772f8001fef000 0x01fc1c000fff8000 0xc03f838001fff000

def z154 : W := mkw 0x9f7eebf00fbd7b01 0xb3efdd7e01f7af60 0xdffce3f00ff87f87 0xdbff9c7e01ff0ff0

def z155 : W := mkw 0x400c6c51b15e0de0 0x08018d8a362bc1bc 0xe01fffffffffffff 0xfc03ffffffffffff

def z156 : W := mkw 0xbdffdbff64802202 0x37bffb7fec900440 0xfffffffffcc06387 0xffffffffff980c70

def z157 : W := mkw 0x022000000ea18001 0x0044000001d43000 0x000000000c018000 0x0000000001803000

def z158 : W := mkw 0xd77403f1bea87fe0 0x9aee807e37d50ffc 0xfffc03f3fff87fe7 0xdfff807e7fff0ffc

def z159 : W := mkw 0xd77c6ff1bffe7fe0 0x9aef8dfe37ffcffc 0xfffcfff3fffe7fe7 0xffff9ffe7fffcffc

def z160 : W := mkw 0x00000004500000a8 0x000000008a000015 0x2000000c70000078 0x040000018e00000f

def z161 : W := mkw 0x977c6ff00ffe7b00 0x92ef8dfe01ffcf60 0xdffcfff00ffe7f87 0xfbff9ffe01ffcff0

def z162 : W := mkw 0x40000001b00004e0 0x080000003600009c 0x20000003f0000060 0x040000007e00000c

def z163 : W := mkw 0x19bbdc0004f28001 0x23377b80009e5000 0x1ffffc0000f80007 0xa3ffff80001f0000

def z164 : W := mkw 0x40ad7c51b5de8de0 0x0815af8a36bbd1bc 0xe1fffcf3ffff9fe7 0xfc3fff9e7ffff3fc

def z165 : W := mkw 0xbddfdbff700022aa 0x37bbfb7fee000455 0xfffffffff00063ff 0xbffffffffe000c7f

def z166 : W := mkw 0x3fbbfe8a8ff7d451 0x67f77fd151fefa8a 0x1ffffcc38fff9c07 0xe3ffff9871fff380

def z167 : W := mkw 0x2802a00a81050450 0x450054015020a08a 0x0000e00380000000 0x00001c0070000000

def z168 : W := mkw 0x133400500ea80900 0x0266800a01d50120 0xdffc00f00ff81f87 0xdbff801e01ff03f0

def z169 : W := mkw 0x199fd85120000000 0x2333fb0a24000000 0xbffffcf3f0000007 0xb7ffff9e7e000000

def z170 : W := mkw 0xbdffdfff64c28002 0x37bffbffec985000 0xbffffffffcc78007 0xf7ffffffff98f000

def z171 : W := mkw 0x40086c01b15604e0 0x08010d80362ac09c 0xe000fc33f0c603e4 0xfc001f867e18c07c

def z172 : W := mkw 0x977003a00ea07200 0x92ee007401d40e40 0x1ffc03000ff86007 0xc3ff806001ff0c00

def z173 : W := mkw 0xaccfdbff60000002 0x3599fb7fec000000 0xa003fffff0000000 0x34007ffffe000000

def z174 : W := mkw 0xbfdffbff6b350003 0x37fbff7fed66a000 0xbffffffff3380007 0xb7fffffffe670000

def z175 : W := mkw 0x00e111244480a208 0x001c222488901441 0x01e3030c0c01e01a 0x003c606181803c03

def z176 : W := mkw 0x020020008b055450 0x404004001160aa8a 0xe003030c0f07fc7e 0x7c00606181e0ff8f

def z177 : W := mkw 0x977423f08fac7f40 0x92ee847e11f58fe8 0xfffce3f38ffe7fe7 0xffff9c7e71ffcffc

def z178 : W := mkw 0x40086c01b15604e0 0x08010d80362ac09c 0xe000fcc3f3061c65 0x7c001f987e60c38c

def z179 : W := mkw 0x1b9bfc000b778001 0x23737f80016ef000 0x1e1ffc00033f8001 0x23c3ff800067f000

def z180 : W := mkw 0x0020040014c2a2a8 0x0004008002985455 0xe0001c307cc7e3fc 0xfc0003860f98fc7f

def z181 : W := mkw 0x400c6851a11c0d40 0x08018d0a342381a8 0x001ce0c383381c01 0x00039c1870670380

def z182 : W := mkw 0xbddfdfff704280aa 0x37bbfbffee085015 0xbffffffff007807f 0xb7fffffffe00f00f

def z183 : W := mkw 0x00e1112444802200 0x001c222488900440 0xe1e31f3c7cc06386 0xfc3c63e78f980c70

def z184 : W := mkw 0xbf1ecadb2a285902 0xb7e3d95b65450b20 0x1e1ce0c383381c01 0x03c39c1870670380

def z185 : W := mkw 0x2e02828a0a005000 0x05c0505141400a00 0xfe03e3cf8f007c07 0x7fc07c79f1e00f80

def z186 : W := mkw 0x0000000000000000 0x0000000000000000 0x2003000c00078078 0x240060018000f00f

def z187 : W := mkw 0x00400124500022a8 0x000800248a000455 0x0000003070000380 0x000000060e000070

def z188 : W := mkw 0x1bb394000ee38001 0x2376728001dc7000 0x1fe31c000cc78006 0xe3fc63800198f000

def z189 : W := mkw 0x24e117aed4c2f6f8 0x449c22f5da985edf 0xe1e31ffffcc7fffe 0xfc3c63ffff98ffff

def z190 : W := mkw 0x0400028000005000 0x0080005000000a00 0xc00003c000007c00 0x1800007800000f80

def z191 : W := mkw 0xffffffffffff8de3 0x3ffffffffffff1bc 0xffffffffffff9fe7 0xfffffffffffff3fc

def z192 : W := mkw 0x91fd5d7574c2a2aa 0x323fabaeae985455 0xe1ff1f3c7cc7e3fe 0xfc3fe3e78f98fc7f

def z193 : W := mkw 0x3bbbfc0f6ff78003 0x27777f81edfef000 0x3ffffc0fffff8007 0xe7ffff81fffff000

def z194 : W := mkw 0x2cc393ae40000000 0x05987275c8000000 0xbfe3fffff0000007 0xb7fc7ffffe000000

def z195 : W := mkw 0x00000400104200a0 0x0000008002084014 0x00001c3070c00380 0x800003860e180070

def z196 : W := mkw 0x00a97c0005d68000 0x00152f8000bad000 0x01fffc000fff8007 0xe03fff8001fff000

def z197 : W := mkw 0x0004005000080900 0x0000800a00010120 0xc00000f000001f80 0x1800001e000003f0

def z198 : W := mkw 0x022024000ff78001 0x0044048001fef000 0x000000000fff8000 0x4000000001fff000

def z199 : W := mkw 0x199bd80000000000 0x23337b0000000000 0x1ffffc0000000007 0xa3ffff8000000000

def z200 : W := mkw 0x088bfc04515780a9 0x21117f808a2af015 0x2003fc0c70078078 0x24007f818e00f00f

def z201 : W := mkw 0x402c6c51b5deafe8 0x08058d8a36bbd5fd 0xe01cfcf3fffffffd 0xfc039f9e7fffffff

def z202 : W := mkw 0x688bfc0ff15604e2 0x2d117f81fe2ac09c 0x2003fc0ff0060060 0x24007f81fe00c00c

def z203 : W := mkw 0x977403f00ea87b00 0x92ee807e01d50f60 0x1ffc00f003f81f81 0x83ff801e007f03f0

def z204 : W := mkw 0x971002800a205000 0x92e2005001440a00 0x1e00000000000000 0x03c0000000000000

def z205 : W := mkw 0x2e02828a8a015450 0x45c0505151402a8a 0xfe0303cf8c01fc7a 0x1fc06079f1803f8f

def z206 : W := mkw 0x1bbbfc001ff780a1 0x23777f8003fef014 0xfffffc307fff83e7 0xffffff860ffff07c

def z207 : W := mkw 0x840402d000085900 0x9080805a00010b20 0x000000c000001c00 0x0000001800000380

def z208 : W := mkw 0x0aabfc000ff78001 0x21557f8001fef000 0x0003fc000fff8000 0x60007f8001fff000

def z209 : W := mkw 0xbddfdbff60000002 0x37bbfb7fec000000 0x1fff1f3c70000002 0x83ffe3e78e000000

def z210 : W := mkw 0x1bbbfc045ff780a9 0x23777f808bfef015 0x3ffffc0c7fff807f 0xe7ffff818ffff00f

def z211 : W := mkw 0x022024009fc7f6f8 0x4044048013f8fedf 0x400000000fc7fff8 0x4800000001f8ffff

def z212 : W := mkw 0x0000200081040440 0x0000040010208088 0xe000e0c383061c65 0x7c001c187060c38c

def z213 : W := mkw 0x1bbbdc000ef38001 0x23777b8001de7000 0x1fff1c000cf98002 0x83ffe380019f3000

def z214 : W := mkw 0x688ffc5ff15e0de2 0x2d11ff8bfe2bc1bc 0xe01ffcfff3fe1fe5 0xfc03ff9ffe7fc3fc

def z215 : W := mkw 0xbf76a3fa8fad7f50 0xd7eed47f51f5afea 0xdffce3f38ff87f87 0xdbff9c7e71ff0ff0

def z216 : W := mkw 0xbddfdbff60000002 0x37bbfb7fec000000 0x1fffe3cf80000003 0x03fffc79f0000000

def z217 : W := mkw 0xbd12828a00000002 0x37a2505140000000 0x1e00000000000000 0x03c0000000000000

def z218 : W := mkw 0x971402d00a285900 0x92e2805a01450b20 0xde1c00f003f81f85 0xdbc3801e007f03f0

def z219 : W := mkw 0x2802a00a81050450 0x450054015020a08a 0xe003e30f8c07e07e 0x7c007c61f180fc0f

def z220 : W := mkw 0x28e3b52ed5c7a6f8 0x451c76a5dab8f4df 0xe1e3ff3ffcc7e3fe 0xfc3c7fe7ff98fc7f

def z221 : W := mkw 0xc44403f1b0087fe0 0x9888807e36010ffc 0xe00003f3f0007fe0 0x1c00007e7e000ffc

def z222 : W := mkw 0x1b1280000a210001 0x2362500001442000 0x1e00000000000000 0x03c0000000000000

def z223 : W := mkw 0x288bdc0f704280aa 0x25117b81ee085015 0x2003fc0ff0078078 0x24007f81fe00f00f

def z224 : W := mkw 0x1130000004a00000 0x0226000000940000 0x01fc000000f80000 0x803f8000001f0000

def z225 : W := mkw 0x3f9bfa8a8b055450 0x67f37f515160aa8a 0xffffffcf8f07fc7f 0xfffffff9f1e0ff8f

def z226 : W := mkw 0xbddfdbff60000002 0x37bbfb7fec000000 0x1ffcfcf3f0000001 0x83ff9f9e7e000000

def z227 : W := mkw 0x97f517f45eeafba8 0x92fea2fe8bdd5f75 0xffff1ffc7fffffff 0xffffe3ff8fffffff

def z228 : W := mkw 0xbfbffedb2ff78003 0x37f7ffdb65fef000 0x1ffffcc38fff8007 0xe3ffff9871fff000

def z229 : W := mkw 0x0802800000000000 0x0100500000000000 0x1e03e00000000007 0x23c07c0000000000

def z230 : W := mkw 0x00000000100022a8 0x0000000002000455 0x40000000000063f8 0x0800000000000c7f

def z231 : W := mkw 0x3fbbfe8a8ff7d451 0x67f77fd151fefa8a 0xffffffcf8ffffc7f 0xfffffff9f1ffff8f

def z232 : W := mkw 0x866403f00ea87b00 0x90cc807e01d50f60 0xc00003f00ff87f80 0x5800007e01ff0ff0

def z233 : W := mkw 0xd17c4d7134fa2ba0 0x9a2f89ae269f4574 0x01fc1c3070f80380 0x803f83860e1f0070

def z234 : W := mkw 0xbf16a2da8b2d5d50 0xd7e2d45b5165abaa 0xfe1fe3cf8f3ffc7f 0x7fc3fc79f1e7ff8f

def z235 : W := mkw 0xbdf393ae4480a20a 0x37be7275c8901441 0x1fe3030c0c01e01a 0x03fc606181803c03

def z236 : W := mkw 0x00895c0000528001 0x20112b80000a5000 0x00001c0000000000 0x0000038000000000

def z237 : W := mkw 0xd71c6ad1ab3c5d40 0x9ae38d5a35678ba8 0x1e1ce0c383381c01 0x03c39c1870670380

def z238 : W := mkw 0x9ffffff00ffffb01 0xb3fffffe01ffff60 0xdffffff00fffff87 0xfbfffffe01fffff0

def z239 : W := mkw 0x00e5157454caaba8 0x001ca2ae8a995575 0xe1ff1ffc7fffffff 0xfc3fe3ff8fffffff

def z240 : W := mkw 0x400c6851a11c0d40 0x08018d0a342381a8 0xa01cfcf3f3381c05 0xb4039f9e7e670380

def z241 : W := mkw 0x2e42a3aedb0576f8 0x45c85475db60aedf 0xfe03e3ffff07ffff 0x7fc07c7fffe0ffff

def z242 : W := mkw 0xbfffffffffc7f6fa 0x77fffffffff8fedf 0xffffffffffc7ffff 0xfffffffffff8ffff

def z243 : W := mkw 0x244003aed00076f8 0x44880075da000edf 0xe00003fff0007ff8 0x1c00007ffe000fff

def z244 : W := mkw 0x2000000a80000450 0x440000015000008a 0x2000000f80000078 0x04000001f000000f

def z245 : W := mkw 0x1bb3b4000ff78001 0x2376768001fef000 0x1fe300000fff8002 0x43fc600001fff000

def z246 : W := mkw 0x1bf391244ea1a209 0x237e722489d43441 0x1fe3030c0c01e01a 0x03fc606181803c03

def z247 : W := mkw 0x088bfc0001578001 0x21117f80002af000 0x001ffc0003ff8005 0xe003ff80007ff000

def z248 : W := mkw 0xbff793fe4ea87b02 0xb7fef27fc9d50f60 0xdfff03fc0ff87f87 0xdbffe07f81ff0ff0

def z249 : W := mkw 0x973402d00ea87b00 0x92e6805a01d50f60 0x5e1c00c00ff87f81 0x4bc3801801ff0ff0

def z250 : W := mkw 0x40086c01b15604e0 0x08010d80362ac09c 0x201cfc03f3fe0065 0xe4039f807e7fc00c

def z251 : W := mkw 0x00000000100000a0 0x0000000002000014 0xe0000030700003e0 0x1c0000060e00007c

def z252 : W := mkw 0x00a1140004c28000 0x0014228000985000 0xe1e31f0c0cc7e07e 0xfc3c63e18198fc0f

def z253 : W := mkw 0xfffffffffffe7fe2 0xbfffffffffffcffc 0xfffffffffffe7fe7 0xffffffffffffcffc

def z254 : W := mkw 0x2e02a28a8b055450 0x45c054515160aa8a 0x5e03030c0f07fc7a 0x4bc0606181e0ff8f

def z255 : W := mkw 0x977403f00ea87b00 0x92ee807e01d50f60 0xffff03fc0fffffff 0xffffe07f81ffffff

def z256 : W := mkw 0x3d9bda8a00000000 0x27b37b5140000000 0xbfffffcf80000007 0xb7fffff9f0000000

def z257 : W := mkw 0xbfffdbff6ea00002 0x37fffb7fedd40000 0xbffffffffff80007 0xf7ffffffffff0000

def z258 : W := mkw 0x00e13524d5c6a6e8 0x001c26a49ab8d4dd 0xe1e3ffffffc7ffff 0xfc3c7ffffff8ffff

def z259 : W := mkw 0x00e1152454c2a2a8 0x001c22a48a985455 0xc1e01f307cc06386 0xd83c03e60f980c70

def z260 : W := mkw 0x2e02828a0a015010 0x45c0505141402a02 0xde0303cc0f01fc1f 0x5bc0607981e03f83

def z261 : W := mkw 0x00000400104280a8 0x0000008002085015 0x0000000000078078 0x000000000000f00f

def z262 : W := mkw 0x40040051300809a0 0x0800800a26010134 0x0000003070000380 0x000000060e000070

def z263 : W := mkw 0xbffffffa8fffff51 0xf7ffffff51ffffea 0xffffffff8fffffff 0xfffffffff1ffffff

def z264 : W := mkw 0x00c1112440000000 0x0018222488000000 0x01e3030c00000002 0x003c606180000000

def z265 : W := mkw 0x2a02a00a8b050450 0x454054015160a08a 0x3e03e00f8f07807f 0x67c07c01f1e0f00f

def z266 : W := mkw 0x2ea3b68a8fc7d450 0x45d476d151f8fa8a 0xffe3ffcf8fc7fc7f 0xfffc7ff9f1f8ff8f

def z267 : W := mkw 0x91d1112440000002 0x323a222488000000 0x01e0000000000000 0x003c000000000000

def z268 : W := mkw 0x2e62a3aa8f857650 0x45cc547551f0aeca 0xffe3e3ff8fc7ffff 0xfffc7c7ff1f8ffff

def z269 : W := mkw 0xbddbdbaf60000002 0x37bb7b75ec000000 0x3fe3ff0ff0000002 0x27fc7fe1fe000000

def z270 : W := mkw 0x99dfd97560000002 0x333bfb2eac000000 0x1ffffc3070000007 0xa3ffff860e000000

def z271 : W := mkw 0x9bfffd756ff78003 0x337fffaeadfef000 0x1ffffc307fff8007 0xe3ffff860ffff000

def z272 : W := mkw 0x2c02a28a81055450 0x458054515020aa8a 0xe003e3cf8007fc78 0x3c007c79f000ff8f

def z273 : W := mkw 0x1bb3b0000fa58001 0x2376760001f4b000 0x1fe3e0000f078007 0x63fc7c0001e0f000

def z274 : W := mkw 0x3bbbfc0a8ff78451 0x67777f8151fef08a 0x3ffffc0f8fff807f 0xe7ffff81f1fff00f

def z275 : W := mkw 0x2883900e40000002 0x25107201c8000000 0x0003000c00000000 0x0000600180000000

def z276 : W := mkw 0x1bfbfd245ff7a2a9 0x237f7fa48bfef455 0xffffff3c7fffe3ff 0xffffffe78ffffc7f

def z277 : W := mkw 0xfdfffffff5deafea 0x3fbffffffebbd5fd 0xffffffffffffffff 0xffffffffffffffff

def z278 : W := mkw 0x97f513f44ea8fb08 0x92fea27e89d51f61 0xdfff03fc0ff9ff9f 0xdbffe07f81ff3ff3

def z279 : W := mkw 0x00e1152004c2a200 0x001c22a400985440 0xc1e31f300cc7e386 0xf83c63e60198fc70

def z280 : W := mkw 0x2e8bfe8a8b57d451 0x65d17fd1516afa8a 0xfe03ffcf8f07fc7f 0x7fc07ff9f1e0ff8f

def z281 : W := mkw 0x40084c01305200a0 0x08010980260a4014 0x00001c0070000000 0x000003800e000000

def z282 : W := mkw 0x0a02a0000b050000 0x014054000160a000 0x1e00e00003000001 0x03c01c0000600000

def z283 : W := mkw 0xac4683ff60000002 0x1588d07fec000000 0xbe03e3fff0000007 0x37c07c7ffe000000

def z284 : W := mkw 0x3fb3b28a8fa5d451 0x67f6765151f4ba8a 0xffe3e3cf8f07fc7f 0x7ffc7c79f1e0ff8f

def z285 : W := mkw 0x40000400105a09a0 0x08000080020b4134 0x0000000000f80380 0x00000000001f0070

def z286 : W := mkw 0x000c6851a1040440 0x00018d0a34208088 0xe01cfcf3f3061c65 0xfc039f9e7e60c38c

def z287 : W := mkw 0x4000000090080de0 0x08000000120101bc 0x4000000000001fe0 0x08000000000003fc

def z288 : W := mkw 0x1bbbd8000ea00000 0x23777b0001d40000 0x1ffffc000ff80007 0xe3ffff8001ff0000

def z289 : W := mkw 0x1bfbfd200ff7a201 0x237f7fa401fef440 0xdfffff300fffe387 0xfbffffe601fffc70

def z290 : W := mkw 0x95dd5bf560000002 0x32bbab7eac000000 0x9ffc1ff070000007 0x93ff83fe0e000000

def z291 : W := mkw 0x400c6c51b15604e0 0x08018d8a362ac09c 0xa01cfcf3f0060065 0xb4039f9e7e00c00c

def z292 : W := mkw 0x40042450915e0de0 0x0800848a122bc1bc 0xc01c00f003fe1fe5 0xd803801e007fc3fc

def z293 : W := mkw 0x00c1112440000000 0x0018222488000000 0x01e01c3070000000 0x803c03860e000000

def z294 : W := mkw 0x0008480000000000 0x0001090000000000 0x001cfc0000000005 0xa0039f8000000000

def z295 : W := mkw 0x2802a00a81050450 0x450054015020a08a 0xe003e0cf83079c7d 0x7c007c19f060f38f

def z296 : W := mkw 0x9174017004a82b00 0x922e802e00950560 0xc1fc03300cf86386 0xd83f8066019f0c70

def z297 : W := mkw 0x9f76a3f00fad7b00 0x93eed47e01f5af60 0xdfffe3f00fffff87 0xfbfffc7e01fffff0

def z298 : W := mkw 0xbfdffbff6b050002 0x37fbff7fed60a000 0xbfffffffff078007 0xf7ffffffffe0f000

def z299 : W := mkw 0x0a02a0000b050000 0x014054000160a000 0x1e03e0000f078007 0x63c07c0001e0f000

def z300 : W := mkw 0x0020040004f28001 0x00040080009e5000 0x0000000000f80000 0x00000000001f0000

def z301 : W := mkw 0x0a02a0008b050440 0x014054001160a088 0xfe03e0c38f079c67 0x7fc07c1871e0f38c

def z302 : W := mkw 0x0000000000087b00 0x8000000000010f60 0x4000000000007f80 0x0800000000000ff0

def z303 : W := mkw 0x399bd80f60000002 0x27337b01ec000000 0x3ffffc0ff0000007 0xa7ffff81fe000000

def z304 : W := mkw 0xbfdfdbff6a015012 0x77fbfb7fed402a02 0xbffffffffc01e01f 0xb7ffffffff803c03

def z305 : W := mkw 0xbd5683fa00000000 0x17aad07f40000000 0xbfffe3ff80000007 0xb7fffc7ff0000000

def z306 : W := mkw 0x13b95c000ef28001 0x22772b8001de5000 0x1ffc1c000ff80007 0xc3ff838001ff0000

def z307 : W := mkw 0xa44403ff60087b02 0x9488807fec010f60 0xe00003fff0007f80 0x1c00007ffe000ff0

def z308 : W := mkw 0xae46a3fa8b0d7f50 0xd5c8d47f5161afea 0xfe03e3ff8f07ffff 0x7fc07c7ff1e0ffff

def z309 : W := mkw 0x844403f000000000 0x1088807e00000000 0x800003f000000000 0x1000007e00000000

def z310 : W := mkw 0x0020000004a82b00 0x8004000000950560 0x0000000000f80380 0x00000000001f0070

def z311 : W := mkw 0x97f117a45ee2f2a8 0x92fe22f48bdc5e55 0xffe31f3c7cc7e3fe 0xfffc63e78f98fc7f

def z312 : W := mkw 0x020020008b055450 0x404004001160aa8a 0xe000e0c38f07fc7d 0x7c001c1871e0ff8f

def z313 : W := mkw 0xbdd793ff60000002 0x37baf27fec000000 0xbfe303fff0000002 0x17fc607ffe000000

def z314 : W := mkw 0x3fbbfe8a0ff78001 0x27f77fd141fef000 0xbfffffcf8fff8007 0xf7fffff9f1fff000

def z315 : W := mkw 0xbddfdbff60080902 0x37bbfb7fec010120 0xfffffffff3f81f87 0xfffffffffe7f03f0

def z316 : W := mkw 0x400c6c51b15e0de0 0x08018d8a362bc1bc 0x401ce0c383fe1fe1 0x48039c18707fc3fc

def z317 : W := mkw 0x1bbffc500fff8901 0x2377ff8a01fff120 0xdffffcf00fff9f87 0xfbffff9e01fff3f0

def z318 : W := mkw 0x2e02a28a8b055450 0x45c054515160aa8a 0x1e00e0c383001c01 0x03c01c1870600380

def z319 : W := mkw 0x00086c0081560440 0x00010d80102ac088 0xe01cfcc383fe1c65 0xfc039f98707fc38c

def z320 : W := mkw 0x133000000ea00000 0x0266000001d40000 0x1fe000000c000002 0x03fc000001800000

def z321 : W := mkw 0x400c6c51b15e0de0 0x08018d8a362bc1bc 0xe000fcf3f0061fe0 0x3c001f9e7e00c3fc

def z322 : W := mkw 0x0e02a2800b055000 0x01c054500160aa00 0xde03e3c00f07fc07 0x7bc07c7801e0ff80

def z323 : W := mkw 0x977423f08fad7f50 0xd2ee847e11f5afea 0xdffc03f00fffffff 0xdbff807e01ffffff

def z324 : W := mkw 0x40086c01b15e0de0 0x08010d80362bc1bc 0x6000fc03f3fe1fe0 0x6c001f807e7fc3fc

def z325 : W := mkw 0x0020040014c2a2a8 0x0004008002985455 0x0000000000c00380 0x0000000000180070

def z326 : W := mkw 0x00040450104a09a0 0x0000808a02094134 0xe01c1cf073fe1fe5 0xfc03839e0e7fc3fc

def z327 : W := mkw 0x00a1140454c280a8 0x001422808a985015 0x21e31c0c7cc7807e 0xe43c63818f98f00f

def z328 : W := mkw 0x2e0eeadbab055450 0x45c1dd5b7560aa8a 0xfe1fffffff07fc7f 0xffc3ffffffe0ff8f

def z329 : W := mkw 0xb5dd5bff60000002 0x36bbab7fec000000 0xa1fc1ffff0000000 0x943f83fffe000000

def z330 : W := mkw 0xa4c513ff60000002 0x1498a27fec000000 0xa1e31ffff0000006 0xb43c63fffe000000

def z331 : W := mkw 0xbfdfdbff6a285902 0xb7fbfb7fed450b20 0xbffffffff3381c07 0xb7fffffffe670380

def z332 : W := mkw 0x2c8bda8f60000002 0x25917b51ec000000 0xbe03ffcff0000007 0x37c07ff9fe000000

def z333 : W := mkw 0x40086801a1140440 0x08010d0034228088 0x0000e00380000000 0x00001c0070000000

def z334 : W := mkw 0x0000000000000000 0x0000000000000000 0xc00003000c006006 0x5800006001800c00

def z335 : W := mkw 0x2e02828a0a015010 0x45c0505141402a02 0xfe03030c0c07e07e 0x7fc060618180fc0f

def z336 : W := mkw 0x2ec3b3aecb055450 0x45d87675d960aa8a 0xffe3ffffff07fc7f 0xfffc7fffffe0ff8f

def z337 : W := mkw 0x0060052014c222a0 0x000c00a402984454 0xe1e01f307cc663e6 0xfc3c03e60f98cc7c

def z338 : W := mkw 0x911c485120000002 0x3223890a24000000 0x001c000000000000 0x0003800000000000

def z339 : W := mkw 0x0040012000000000 0x0008002400000000 0x81e0033000000006 0x903c006600000000

def z340 : W := mkw 0x1bbbfc001ff7a2a9 0x23777f8003fef455 0x5ffffc000fffe3ff 0xebffff8001fffc7f

def z341 : W := mkw 0x977407f01eeafba8 0x92ee80fe03dd5f75 0xdffc03f00fffffff 0xdbff807e01ffffff

def z342 : W := mkw 0x680aec0bb15704f0 0x4d015d81762ae09e 0x2003fc0ff0078078 0x24007f81fe00f00f

def z343 : W := mkw 0x00e1152454c2a2a8 0x001c22a48a985455 0xe1e01c3070c603e4 0xfc3c03860e18c07c

def z344 : W := mkw 0x3f32a28a8fa55450 0x47e6545151f4aa8a 0xffffe3cf8ffffc7f 0xfffffc79f1ffff8f

def z345 : W := mkw 0x9ff393a00ea1f201 0xb3fe727401d43e40 0x1fe303000c01e002 0x03fc606001803c00

def z346 : W := mkw 0x2000000f60000002 0x04000001ec000000 0x2000000ff0000000 0x04000001fe000000

def z347 : W := mkw 0x975403f00a285900 0x92ea807e01450b20 0x9ffc03f003381c07 0x93ff807e00670380

def z348 : W := mkw 0x97fd5ff00efafb01 0xb2ffabfe01df5f60 0xdffc1ff00ff87f87 0xdbff83fe01ff0ff0

def z349 : W := mkw 0x9ddfdbf000000000 0x33bbfb7e00000000 0x9ffffff000000007 0xb3fffffe00000000

def z350 : W := mkw 0x84e517f454cafba8 0x909ca2fe8a995f75 0xe1e31ffc7cc7fffe 0xfc3c63ff8f98ffff

def z351 : W := mkw 0x9ffffff00ff78001 0x33fffffe01fef000 0x9ffffff00fff8007 0xf3fffffe01fff000

def z352 : W := mkw 0x1b9bf8000b350001 0x23737f000166a000 0x1ffffc0003380007 0xa3ffff8000670000

def z353 : W := mkw 0x022020008fad7f50 0xc044040011f5afea 0x400000000ffffff8 0x4800000001ffffff

def z354 : W := mkw 0x2c02828a00000000 0x0580505140000000 0x1e00e0c380000001 0x03c01c1870000000

def z355 : W := mkw 0x1b3aec000ff78001 0x23675d8001fef000 0x1e1ce0000fff8001 0x43c39c0001fff000

def z356 : W := mkw 0xbf7ecbfb2ea87b02 0xb7efd97f65d50f60 0xdffce3f38ff87f87 0xdbff9c7e71ff0ff0

def z357 : W := mkw 0x977003a00ea87b00 0x92ee007401d50f60 0x5fe003000ff87f82 0x4bfc006001ff0ff0

def z358 : W := mkw 0x2c02a28a81050450 0x458054515020a08a 0xbe03e3cf8007807f 0x37c07c79f000f00f

def z359 : W := mkw 0x0081100000000000 0x0010220000000000 0x01e31c0000000006 0xa03c638000000000

def z360 : W := mkw 0x11f95d2454f2a2a9 0x223f2ba48a9e5455 0xe1ff1f3c7cffe3fe 0xfc3fe3e78f9ffc7f

def z361 : W := mkw 0x00400524504222a8 0x000800a48a084455 0xe0001f3c70c663fc 0xfc0003e78e18cc7f

def z362 : W := mkw 0x680eec5bb15f0df0 0x4d01dd8b762be1be 0xe01ffcfff3ff9ffd 0xfc03ff9ffe7ff3ff

def z363 : W := mkw 0x95f517f454c2a2a8 0x12bea2fe8a985455 0xffff1ffc7cc7e3ff 0xffffe3ff8f98fc7f

def z364 : W := mkw 0x00086c00115600a0 0x00010d80022ac014 0xe01cfc3073fe03e5 0xfc039f860e7fc07c

def z365 : W := mkw 0x2600228a8b055450 0x44c004515160aa8a 0xe00003cf8f07fc78 0x5c000079f1e0ff8f

def z366 : W := mkw 0x0020000004800000 0x0004000000900000 0x01e000000cc00006 0xc03c000001980000

def z367 : W := mkw 0x6c0eeedbb15e0de0 0x0d81dddb762bc1bc 0xfe1ffffff3fe1fe7 0xffc3fffffe7fc3fc

def z368 : W := mkw 0x40002400915e0de0 0x08000480122bc1bc 0xe000e0c383fe1fe5 0x7c001c18707fc3fc

def z369 : W := mkw 0x1110000000000000 0x0222000000000000 0x1ffc000000000007 0x83ff800000000000

def z370 : W := mkw 0xd1dd5d75705a09a2 0x3a3babaeae0b4134 0x01fc1c3070f80380 0x803f83860e1f0070

def z371 : W := mkw 0x955403f000080900 0x12aa807e00010120 0xdffc03f003f81f87 0xdbff807e007f03f0

def z372 : W := mkw 0x4020240095deafe8 0x0804048012bbd5fd 0x400000000ffffff8 0x4800000001ffffff

def z373 : W := mkw 0xbd5ecbfb20000002 0x37abd97f64000000 0x9ffce3f380000007 0x93ff9c7e70000000

def z374 : W := mkw 0x173002800ea05000 0x02e6005001d40a00 0xdffc03c00ff87c07 0xdbff807801ff0f80

def z375 : W := mkw 0x975403f00a005000 0x12ea807e01400a00 0xdffc03f00f007c07 0xdbff807e01e00f80

def z376 : W := mkw 0x2400028a80005450 0x4480005150000a8a 0xe00303cf8c07fc7e 0x7c006079f180ff8f

def z377 : W := mkw 0x020020000b050000 0x004004000160a000 0x000000000f078000 0x4000000001e0f000

def z378 : W := mkw 0x1bf395245ee3a2a9 0x237e72a48bdc7455 0xffe31f3c7cc7e3fe 0xfffc63e78f98fc7f

def z379 : W := mkw 0x00e1152444c2a208 0x001c22a488985441 0x01e31f0c0cc7e01e 0xe03c63e18198fc03

def z380 : W := mkw 0xa4e517ff74c2a2aa 0x149ca2ffee985455 0xe1e31ffffcc7e3fe 0xfc3c63ffff98fc7f

def z381 : W := mkw 0x2ee397ae5ec3f2b8 0x45dc72f5cbd87e57 0xffe31f3c7cc7e3fe 0xfffc63e78f98fc7f

def z382 : W := mkw 0x00c11124500022a8 0x001822248a000455 0xe1e31f3c700063fe 0xbc3c63e78e000c7f

def z383 : W := mkw 0xbfffdbff6ea18003 0x37fffb7fedd43000 0xbffffffffc018007 0xb7ffffffff803000

def z384 : W := mkw 0x91dd597560000002 0x323bab2eac000000 0xa1ff1f3c70000006 0xb43fe3e78e000000

def z385 : W := mkw 0x977403f00ea87b00 0x92ee807e01d50f60 0x1ffc03c00f387c03 0x03ff807801e70f80

def z386 : W := mkw 0x91f5157454eaaba8 0x923ea2ae8a9d5575 0x01fc1c3070f80380 0x803f83860e1f0070

def z387 : W := mkw 0x08ebfd2455d7a2a9 0x211d7fa48abaf455 0xe1e3ff3c7cc7e3fe 0xfc3c7fe78f98fc7f

def z388 : W := mkw 0x00600124548022a8 0x000c00248a900455 0xe1e0033c7cc063fe 0xdc3c00678f980c7f

def z389 : W := mkw 0x40042451b15e0de0 0x0800848a362bc1bc 0xe00000f3f3fe1fe0 0x5c00001e7e7fc3fc

def z390 : W := mkw 0x40ed7d75f5deafe8 0x081dafaebebbd5fd 0xe1fcfcf3f3fe1fe5 0xfc3f9f9e7e7fc3fc

def z391 : W := mkw 0x400c6c51315e09a0 0x08018d8a262bc134 0x001cfc3073fe0385 0xe0039f860e7fc070

def z392 : W := mkw 0x00086c0001560000 0x00010d80002ac000 0x0000fc0000060000 0x20001f800000c000

def z393 : W := mkw 0xfddfdbfff0080de2 0x3fbbfb7ffe0101bc 0xfffffffff0001fe7 0xbffffffffe0003fc

def z394 : W := mkw 0x2802800a00000000 0x0500500140000000 0x2003e00f80000000 0x24007c01f0000000

def z395 : W := mkw 0x060022808b045440 0x00c0045011608a88 0xfe00e3c38f067c67 0x7fc01c7871e0cf8c

def z396 : W := mkw 0x3fb3928a0ea1d011 0x67f6725141d43a02 0x1fe3030c0c01e01a 0x03fc606181803c03

def z397 : W := mkw 0xfddfdfff705a09a2 0x3fbbfbffee0b4134 0xbffffffff0f80387 0xb7fffffffe1f0070

def z398 : W := mkw 0xa40402db20000002 0x1480805b64000000 0x000000c380000000 0x0000001870000000

def z399 : W := mkw 0x060002800a005000 0x00c0005001400a00 0x1e0000c003001c01 0x03c0001800600380

def z400 : W := mkw 0x0000000080005450 0x4000000010000a8a 0x4000000000007c78 0x0800000000000f8f

def z401 : W := mkw 0x599ffc51b15e0de0 0x2b33ff8a362bc1bc 0xfffffcf3f3fe1fe7 0xffffff9e7e7fc3fc

def z402 : W := mkw 0x00e1152444c28000 0x001c22a488985000 0xa1e31f3c7cc78006 0xf43c63e78f98f000

def z403 : W := mkw 0xbddffbffe1050452 0x77bbff7ffc20a08a 0xbffffffff007807f 0xb7fffffffe00f00f

def z404 : W := mkw 0x00811404504280a8 0x001022808a085015 0xe0031f0c7c07e07e 0x7c0063e18f80fc0f

def z405 : W := mkw 0x2ce397ae54c2a2a8 0x059c72f5ca985455 0xffe3fffffcc7e3ff 0xfffc7fffff98fc7f

def z406 : W := mkw 0x971402d00a285900 0x92e2805a01450b20 0xde1c03c00f387c07 0x5bc3807801e70f80

def z407 : W := mkw 0x0004005000080900 0x0000800a00010120 0x001c00c003381c01 0x0003801800670380

def z408 : W := mkw 0x977003a00ea07200 0x92ee007401d40e40 0xdfe003300cc06386 0xdbfc006601980c70

def z409 : W := mkw 0x000c485120000000 0x0001890a24000000 0x001ce0c380000001 0x00039c1870000000

def z410 : W := mkw 0x066003a00e807200 0x00cc007401d00e40 0xdfe003f00fc07f87 0xdbfc007e01f80ff0

def z411 : W := mkw 0x9174017004a82b00 0x922e802e00950560 0xc1fc00f003f81f85 0xd83f801e007f03f0

def z412 : W := mkw 0x199bfc0001560000 0x23337f80002ac000 0x1ffffc0003fe0007 0xe3ffff80007fc000

def z413 : W := mkw 0x40086c00915e0de0 0x08010d80122bc1bc 0x401cfc0003fe1fe5 0xe8039f80007fc3fc

def z414 : W := mkw 0x422024009ffe7fe0 0x8844048013ffcffc 0x400000000ffe7fe0 0x4800000001ffcffc

def z415 : W := mkw 0x00c11524504280a8 0x001822a48a085015 0xa1e31f3c7007807e 0xb43c63e78e00f00f

def z416 : W := mkw 0x13b114000ee28000 0x0276228001dc5000 0x1fff1c000fff8007 0xe3ffe38001fff000

def z417 : W := mkw 0x00e1152454c2a2a8 0x001c22a48a985455 0x41e3030c0cc7e3fa 0x483c60618198fc7f

def z418 : W := mkw 0xbddfdbff60000002 0x37bbfb7fec000000 0xfffffffffc07e07f 0xffffffffff80fc0f

def z419 : W := mkw 0x19bbfc0005f78001 0x23377f8000bef000 0x01fffc0000ff8000 0xa03fff80001ff000

def z420 : W := mkw 0x020000000a005000 0x0040000001400a00 0x400000000f007c00 0x4800000001e00f80

def z421 : W := mkw 0x5bbbfc01bff784e1 0x2b777f8037fef09c 0x3ffffc03ffff8067 0xe7ffff807ffff00c

def z422 : W := mkw 0x1bbbfc008ff7d451 0x63777f8011fefa8a 0x5ffffc000ffffc7f 0xebffff8001ffff8f

def z423 : W := mkw 0x957403f004a87b00 0x92ae807e00950f60 0xc1fc03f000f87f80 0x983f807e001f0ff0

def z424 : W := mkw 0xd17c6d71b5fe2fe0 0x9a2f8dae36bfc5fc 0xe1fcfcf3f3fe1fe5 0xfc3f9f9e7e7fc3fc

def z425 : W := mkw 0x2ee3b3aecf85f658 0x45dc7675d9f0becb 0xffe3e3cf8f07fc7f 0x7ffc7c79f1e0ff8f

def z426 : W := mkw 0x0004005000080900 0x0000800a00010120 0x001c003000f80380 0x80038006001f0070

def z427 : W := mkw 0x955003a000000000 0x12aa007400000000 0x1fe0030000000002 0x03fc006000000000

def z428 : W := mkw 0x00a1140004c28000 0x0014228000985000 0x01e01c0000c00000 0x803c038000180000

def z429 : W := mkw 0x400c6c51b15e0de0 0x08018d8a362bc1bc 0x401c1c3073fe1fe0 0xc80383860e7fc3fc

def z430 : W := mkw 0xa44403ffe0005452 0x5488807ffc000a8a 0xe00003fff0007c78 0x1c00007ffe000f8f

def z431 : W := mkw 0x0000000000080900 0x0000000000010120 0x4000000003f81f80 0x48000000007f03f0

def z432 : W := mkw 0x40897c05f15684e8 0x08112f80be2ad09d 0x2003fc0ff0078078 0x24007f81fe00f00f

def z433 : W := mkw 0x1b3ae8000fb50001 0x23675d0001f6a000 0x1ffce0000ff80007 0xc3ff9c0001ff0000

def z434 : W := mkw 0x488ffc51b15f8de1 0x2911ff8a362bf1bc 0xe01ffcf3f3ff9fe5 0xfc03ff9e7e7ff3fc

def z435 : W := mkw 0x400c6c51b15e0de0 0x08018d8a362bc1bc 0x201cfc33f0fe03e0 0xa4039f867e1fc07c

def z436 : W := mkw 0x0000200081040440 0x0000040010208088 0xe003e3cf8f07fc7f 0x7c007c79f1e0ff8f

def z437 : W := mkw 0x000c6c5121560000 0x00018d8a242ac000 0xa01cfcf3f3fe0005 0xf4039f9e7e7fc000

def z438 : W := mkw 0x0aa3b4000fc78000 0x0154768001f8f000 0x1fe3fc000fc78007 0xe3fc7f8001f8f000

def z439 : W := mkw 0x00e1152454c2a2a8 0x001c22a48a985455 0x41e01c307cc7e3f8 0xc83c03860f98fc7f

def z440 : W := mkw 0xbd9fdadf60000002 0x37b3fb5bec000000 0x3e1ffccff0000001 0x27c3ff99fe000000

def z441 : W := mkw 0x280ac80b20000002 0x2501590164000000 0x0000e00380000000 0x00001c0070000000

def z442 : W := mkw 0x1993900000000000 0x2332720000000000 0x1fe3000000000002 0x03fc600000000000

def z443 : W := mkw 0x00e111244480a208 0x001c222488901441 0xe1e3030c0c07e07e 0x7c3c60618180fc0f

def z444 : W := mkw 0x06e117a45ec2f2a8 0x00dc22f48bd85e55 0xffe31ffc7fc7ffff 0xfffc63ff8ff8ffff

def z445 : W := mkw 0x131000000a200000 0x0262000001440000 0x1e1c000003380001 0x03c3800000670000

def z446 : W := mkw 0x00e1152454c2a2a8 0x001c22a48a985455 0xe1e01f3c70c063f8 0x9c3c03e78e180c7f

def z447 : W := mkw 0x1b1ae8000b350001 0x23635d000166a000 0x1e1fe0000f3f8007 0x63c3fc0001e7f000

def z448 : W := mkw 0x002000000480a208 0x0004000000901441 0x000000000c01e018 0x0000000001803c03

def z449 : W := mkw 0x9ffffff45ffffba9 0xb3fffffe8bffff75 0xfffffffc7fffffff 0xffffffff8fffffff

def z450 : W := mkw 0x6eefffffffdffff8 0x4dddfffffffbffff 0xffffffffffffffff 0xffffffffffffffff

def z451 : W := mkw 0xbfdffbffeb055452 0x77fbff7ffd60aa8a 0xbffffffff3001c07 0xb7fffffffe600380

def z452 : W := mkw 0x408d7c55f15e8de8 0x0811af8abe2bd1bd 0xe01ffcfff3ff9ffd 0xfc03ff9ffe7ff3ff

def z453 : W := mkw 0x4a0eec51bb5f0de0 0x0941dd8a376be1bc 0xfe1ffcf3ffff9fe7 0xffc3ff9e7ffff3fc

def z454 : W := mkw 0x11b97c0005f68001 0x22372f8000bed000 0x01fcfc0003fe0005 0xe03f9f80007fc000

def z455 : W := mkw 0x0400028000000000 0x0080005000000000 0x9e0003c000000007 0x13c0007800000000

def z456 : W := mkw 0xbfffdbff6ea07202 0xb7fffb7fedd40e40 0xbffffffffc006007 0xb7ffffffff800c00

def z457 : W := mkw 0xbf56a3fa8b055450 0x57ead47f5160aa8a 0xffffe3ff8f07fc7f 0xfffffc7ff1e0ff8f

def z458 : W := mkw 0x400c6851b11c0de0 0x08018d0a362381bc 0xe01ce0f3f3381fe1 0x1c039c1e7e6703fc

def z459 : W := mkw 0x0000200001040000 0x0000040000208000 0x0000e00003060005 0x60001c000060c000

def z460 : W := mkw 0x40ed5d7574daaba8 0x081dabaeae9b5575 0x01fc1c3070f80380 0x803f83860e1f0070

def z461 : W := mkw 0x420024009b5f5df0 0x48400480136bebbe 0x400000000ffffff8 0x4800000001ffffff

def z462 : W := mkw 0x2e22a28a8fad7f50 0xc5c4545151f5afea 0xfe03e3cf8fffffff 0x7fc07c79f1ffffff

def z463 : W := mkw 0x00e1152454c2a2a8 0x001c22a48a985455 0xa1e31f3c70c00386 0xb43c63e78e180070

def z464 : W := mkw 0xbd5ecbff60000002 0x37abd97fec000000 0xbe1ce3fff0000001 0x17c39c7ffe000000

def z465 : W := mkw 0x40440175f0082fe8 0x0808802ebe0105fd 0xe00003fff0007ff8 0x1c00007ffe000fff

def z466 : W := mkw 0x022000000ea00000 0x0044000001d40000 0x000000000ff80000 0x4000000001ff0000

def z467 : W := mkw 0x2802800a00010010 0x4500500140002002 0x0003000c00018018 0x0000600180003003

def z468 : W := mkw 0xbfffffffeff7d453 0x77fffffffdfefa8a 0xfffffffffffffc7f 0xffffffffffffff8f

def z469 : W := mkw 0x0883900000018001 0x2110720000003000 0x0003000000018000 0x0000600000003000

def z470 : W := mkw 0xb77403fa8ea87f50 0xd6ee807f51d50fea 0xfffc03ff8ff87fff 0xdfff807ff1ff0fff

def z471 : W := mkw 0x406c6d71b5de2fe0 0x080d8dae36bbc5fc 0xe1fcfff3fffe7fe7 0xfc3f9ffe7fffcffc

def z472 : W := mkw 0xd71c6ed1bb7e5de0 0x9ae38dda376fcbbc 0xfe1cfcf3f3fe1fe5 0xffc39f9e7e7fc3fc

def z473 : W := mkw 0x9f1eead00b3d5901 0xb3e3dd5a0167ab20 0x1e1ce0c003381c01 0x03c39c1800670380

def z474 : W := mkw 0xbdf397ae54c2a2aa 0x37be72f5ca985455 0xffe31f3c7cc7e3fe 0xfffc63e78f98fc7f

def z475 : W := mkw 0x97f517f00eeafb00 0x92fea2fe01dd5f60 0xdfff1ff00fffff87 0xfbffe3fe01fffff0

def z476 : W := mkw 0x40002400915e0de0 0x08000480122bc1bc 0xe0001c3073fe1fe4 0xfc0003860e7fc3fc

def z477 : W := mkw 0x0000000000000000 0x0000000000000000 0xa000e0c380000005 0x34001c1870000000

def z478 : W := mkw 0xa44c4bff60000002 0x1489897fec000000 0xa01cfffff0000005 0xb4039ffffe000000

def z479 : W := mkw 0x40040051b0080de0 0x0800800a360101bc 0xe01c00f3f3f81fe5 0xdc03801e7e7f03fc

def z480 : W := mkw 0x955403f000087b00 0x92aa807e00010f60 0xdffc03f000007f87 0x9bff807e00000ff0

def z481 : W := mkw 0x0060052014c2a2a8 0x000c00a402985455 0xc1e003300cc7e3fe 0xd83c00660198fc7f

def z482 : W := mkw 0x2e8bfa8feb055452 0x65d17f51fd60aa8a 0xfe03ffcfff07fc7f 0x7fc07ff9ffe0ff8f

def z483 : W := mkw 0x400c6c51b15e0de0 0x08018d8a362bc1bc 0x001cfcf3f3f81f81 0x80039f9e7e7f03f0

def z484 : W := mkw 0x977c4bf12ea87b00 0x92ef897e25d50f60 0xfffcfff3fff87f87 0xffff9ffe7fff0ff0

def z485 : W := mkw 0x28cbd92f60000002 0x25197b25ec000000 0xa1e3ff3ff0000006 0xb43c7fe7fe000000

def z486 : W := mkw 0x0a02a0008b055450 0x414054001160aa8a 0x5e03e0000f07fc7f 0x6bc07c0001e0ff8f

def z487 : W := mkw 0x28ebdd2f74c2a2aa 0x251d7ba5ee985455 0xe1e3ff3ffcc7e3fe 0xfc3c7fe7ff98fc7f

def z488 : W := mkw 0x020020008b055450 0x404004001160aa8a 0x0000000003001c00 0x0000000000600380

def z489 : W := mkw 0x844403f450087ba8 0x9088807e8a010f75 0xe00003fc70007ff8 0x1c00007f8e000fff

def z490 : W := mkw 0x6e06a2dbbb0d5df0 0x4dc0d45b7761abbe 0xfe03e3ffff07ffff 0x7fc07c7fffe0ffff

def z491 : W := mkw 0xbf1eeadbab055452 0x77e3dd5b7560aa8a 0x1e1ce0c383001c01 0x03c39c1870600380

def z492 : W := mkw 0xbfffffff7ff7a2ab 0x37ffffffeffef455 0xffffffffffffe3ff 0xfffffffffffffc7f

def z493 : W := mkw 0x1bbbfc008ff78441 0x23777f8011fef088 0xfffffcc38fff9c67 0xffffff9871fff38c

def z494 : W := mkw 0x00a1140014c2a2a8 0x0014228002985455 0x41e31c000cc7e3fe 0xe83c63800198fc7f

def z495 : W := mkw 0xbf7683fa0ea87b00 0x97eed07f41d50f60 0xffffe3ff8ff87f87 0xfffffc7ff1ff0ff0

def z496 : W := mkw 0x0008480120000000 0x0001090024000000 0x2000fc03f0000000 0x24001f807e000000

def z497 : W := mkw 0x8044017000082b00 0x9008802e00010560 0x0000003000000380 0x0000000600000070

def z498 : W := mkw 0x9fffdbf00ea87b00 0xb3fffb7e01d50f60 0xdffffff00ff87f87 0xfbfffffe01ff0ff0

def z499 : W := mkw 0x957403f004a82b00 0x92ae807e00950560 0x9ffc03f000f80387 0x93ff807e001f0070

def z500 : W := mkw 0xfddffffff15604e2 0x3fbbfffffe2ac09c 0xbffffffff0060067 0xb7fffffffe00c00c

def z501 : W := mkw 0xbff7b7fedfeffff8 0xd7fef6ffdbfdffff 0xffffffffffffffff 0xffffffffffffffff

def z502 : W := mkw 0x951402d000000000 0x12a2805a00000000 0x1e1c00c000000001 0x03c3801800000000

def z503 : W := mkw 0x2e06a2da8b0d5d50 0x45c0d45b5161abaa 0xfe1fe3ff8fffffff 0xffc3fc7ff1ffffff

def z504 : W := mkw 0x0ae3b5245fc7a2a8 0x015c76a48bf8f455 0xffe3ff3c7fc7e3ff 0xfffc7fe78ff8fc7f

def z505 : W := mkw 0x3fbbfe8a0ff7d011 0x67f77fd141fefa02 0x1fffff0c0fffe01f 0xe3ffffe181fffc03

def z506 : W := mkw 0x0000000000000000 0x0000000000000000 0xe000030c00006078 0x1c00006180000c0f

def z507 : W := mkw 0x846403f004887b00 0x908c807e00910f60 0xc1e003f00cc07f86 0xd83c007e01980ff0

def z508 : W := mkw 0x00002400914604e0 0x000004801228c09c 0xe000fcf3f3c61fe5 0xfc001f9e7e78c3fc

def z509 : W := mkw 0x00e111244480a208 0x001c222488901441 0xc1e3033c0cc1e39e 0xd83c606781983c73

def z510 : W := mkw 0x5bbffc513fff89a1 0x2b77ff8a27fff134 0x1ffffc307fff8387 0xe3ffff860ffff070

def z511 : W := mkw 0x0000040000420000 0x0000008000084000 0x00001c0000c60004 0xe00003800018c000

def z512 : W := mkw 0x2e0aee8a8b575450 0x45c15dd1516aea8a 0xfe1fffcf8ffffc7f 0xffc3fff9f1ffff8f

def z513 : W := mkw 0xbd9fdadb20000002 0x37b3fb5b64000000 0x1ffffcc380000007 0xa3ffff9870000000

def z514 : W := mkw 0x2ee393ae4e81f218 0x45dc7275c9d03e43 0x1fe3030c0c01e01a 0x03fc606181803c03

def z515 : W := mkw 0x00a1140014c280a0 0x0014228002985014 0xe1e31c307cc783e6 0xfc3c63860f98f07c

def z516 : W := mkw 0xe44c6ffff15e0de2 0x1c898dfffe2bc1bc 0xe01cfffff3fe1fe5 0xfc039ffffe7fc3fc

def z517 : W := mkw 0xfd1eeadba11c0d42 0x3fa3dd5b742381a8 0x1e1ce0c383381c01 0x03c39c1870670380

def z518 : W := mkw 0x40040451b04a0de0 0x0800808a360941bc 0xe0001cf3f0c61fe4 0xfc00039e7e18c3fc

def z519 : W := mkw 0x02e13524dfc7f6f8 0x405c26a49bf8fedf 0xe1e31f3c7fc7fffe 0xfc3c63e78ff8ffff

def z520 : W := mkw 0x3f1aea8a8b355451 0x67e35d515166aa8a 0xfe1fe3cf8f3ffc7f 0x7fc3fc79f1e7ff8f

def z521 : W := mkw 0xbdffdfff74c2a2aa 0x37bffbffee985455 0xbffffffff0c00387 0xb7fffffffe180070

def z522 : W := mkw 0x1199580000000000 0x22332b0000000000 0x01fc1c0000000000 0x803f838000000000

def z523 : W := mkw 0x400c4c51305a09a0 0x0801898a260b4134 0xe01c1c3070fe03e4 0xfc0383860e1fc07c

def z524 : W := mkw 0x02a134000ff78001 0x0054268001fef000 0x01e31c000fff8006 0xe03c638001fff000

def z525 : W := mkw 0x0000200081040440 0x0000040010208088 0x2000e00380060060 0x24001c007000c00c

def z526 : W := mkw 0x191ac80000000000 0x2323590000000000 0x1e1ce00000000001 0x03c39c0000000000

def z527 : W := mkw 0x022024000ffffb01 0x8044048001ffff60 0x400000000fffff80 0x4800000001fffff0

def z528 : W := mkw 0x00000400104200a0 0x0000008002084014 0xe0031f3c7cc7e3fe 0xfc0063e78f98fc7f

def z529 : W := mkw 0xbfffffff6ffffb03 0xb7ffffffedffff60 0xffffffffffffff87 0xfffffffffffffff0

def z530 : W := mkw 0x1fbbfe800ff7d001 0x23f77fd001fefa00 0xdfffffc00ffffc07 0xfbfffff801ffff80

def z531 : W := mkw 0xd1dd7d75f15e0de2 0x3a3bafaebe2bc1bc 0xe1fcfcf3f3fe1fe5 0xfc3f9f9e7e7fc3fc

def z532 : W := mkw 0xd55c6ff1b15e0de0 0x1aab8dfe362bc1bc 0xfffcfff3f3fe1fe7 0xffff9ffe7e7fc3fc

def z533 : W := mkw 0x95d513f440000000 0x12baa27e88000000 0xbfff1ffc70000007 0xb7ffe3ff8e000000

def z534 : W := mkw 0x00000400104200a0 0x0000008002084014 0x4000000000c603e0 0x480000000018c07c

def z535 : W := mkw 0xbfdfdbff6a005002 0x37fbfb7fed400a00 0xffffffffff007c07 0xffffffffffe00f80

def z536 : W := mkw 0x404c6d75f15e2fe8 0x08098daebe2bc5fd 0xe01cfffff3fe7ffd 0xfc039ffffe7fcfff

def z537 : W := mkw 0x51bd7c51b5fe8de1 0x2a37af8a36bfd1bc 0xe1fcfcf3f3fe1fe5 0xfc3f9f9e7e7fc3fc

def z538 : W := mkw 0x9170012004a02200 0x922e002400940440 0x01e0000000000000 0x003c000000000000

def z539 : W := mkw 0x40e51575f4caafe8 0x081ca2aebe9955fd 0xe1e31ffffcc7fffe 0xfc3c63ffff98ffff

def z540 : W := mkw 0x2e02a28a8b055450 0x45c054515160aa8a 0xfe00e3cf83007c79 0x1fc01c79f0600f8f

def z541 : W := mkw 0x020020000b350001 0x004004000166a000 0x0000000003380000 0x0000000000670000

def z542 : W := mkw 0x977403f00ea00000 0x12ee807e01d40000 0x9ffc03f00ff80007 0xd3ff807e01ff0000

def z543 : W := mkw 0xbddfdfff704200a2 0x37bbfbffee084014 0xfffffffff0c603e7 0xfffffffffe18c07c

def z544 : W := mkw 0x088bd80000000000 0x21117b0000000000 0x0003fc0000000000 0x20007f8000000000

def z545 : W := mkw 0x13f115245ee2a2a8 0x027e22a48bdc5455 0xffff1f3c7fffe3ff 0xffffe3e78ffffc7f

def z546 : W := mkw 0xbfd393ae4a015012 0x77fa7275c9402a02 0x1fe3030c0c01e01a 0x03fc606181803c03

def z547 : W := mkw 0x973402d00ea85900 0x92e6805a01d50b20 0x1ffc00c00ff81c07 0xc3ff801801ff0380

def z548 : W := mkw 0x2c02828a00000000 0x0580505140000000 0xfe03e3cf8c07e07f 0x7fc07c79f180fc0f

def z549 : W := mkw 0x8044017560000002 0x1008802eac000000 0x0000003070000000 0x000000060e000000

def z550 : W := mkw 0x2e22a68a8ff7d451 0x45c454d151fefa8a 0xfe03e3cf8ffffc7f 0x7fc07c79f1ffff8f

def z551 : W := mkw 0x2c02828a80005450 0x4580505150000a8a 0xfe03e3cf80007c7f 0x3fc07c79f0000f8f

def z552 : W := mkw 0xd77c4ff13efa7ba0 0x9aef89fe27df4f74 0xdffc1ff07ff87f87 0xdbff83fe0fff0ff0

def z553 : W := mkw 0x0060012004802200 0x000c002400900440 0xe1e3033c0cc7e3fe 0xfc3c60678198fc7f

def z554 : W := mkw 0x000c6c50015e0900 0x00018d8a002bc120 0xc01cfcf003fe1f85 0xf8039f9e007fc3f0

def z555 : W := mkw 0x00e111244480a208 0x001c222488901441 0xa1e31f3c7c01e01e 0xb43c63e78f803c03

def z556 : W := mkw 0x0000000000000000 0x0000000000000000 0xe000000000060064 0x7c0000000000c00c

def z557 : W := mkw 0xd77c6bf1afbc7f40 0x9aef8d7e35f78fe8 0xdffce3f38ff87f87 0xdbff9c7e71ff0ff0

def z558 : W := mkw 0x020000000a285900 0x8040000001450b20 0x0000000003381c00 0x0000000000670380

def z559 : W := mkw 0x288bf80fe1050452 0x65117f01fc20a08a 0x2003fc0ff0078078 0x24007f81fe00f00f

def z560 : W := mkw 0x400c4c51305a09a0 0x0801898a260b4134 0xc01c1cf073f81f85 0xd803839e0e7f03f0

def z561 : W := mkw 0x0a8bfc000b578001 0x21517f80016af000 0x1e03fc000f078007 0x63c07f8001e0f000

def z562 : W := mkw 0x0000200081040440 0x0000040010208088 0x0000e0c383001c01 0x00001c1870600380

def z563 : W := mkw 0x026001200ea87b00 0x804c002401d50f60 0xc1e003300ff87f86 0xd83c006601ff0ff0

def z564 : W := mkw 0x6e0eeadbab1d5d50 0x4dc1dd5b7563abaa 0x1e1ce0c383381c01 0x03c39c1870670380

def z565 : W := mkw 0x0089580560000002 0x20112b00ac000000 0x00001c0070000000 0x000003800e000000

def z566 : W := mkw 0xbd1ecadb20000002 0x37a3d95b64000000 0xbe1fe3cf80000007 0x37c3fc79f0000000

def z567 : W := mkw 0x0060012004802200 0x000c002400900440 0x01e003000c006002 0x003c006001800c00

def z568 : W := mkw 0x2e02a28a8b055450 0x45c054515160aa8a 0x5e00e0c38f07fc79 0x4bc01c1871e0ff8f

def z569 : W := mkw 0x400c4851b0080de0 0x0801890a360101bc 0xe01cfcf3f0001fe5 0xbc039f9e7e0003fc

def z570 : W := mkw 0x40e13524d5deafe8 0x081c26a49abbd5fd 0xe1e31f3c7ffffffe 0xfc3c63e78fffffff

def z571 : W := mkw 0x0a0aec000b570000 0x01415d80016ae000 0x1e1ffc000fff8007 0xe3c3ff8001fff000

def z572 : W := mkw 0x00e111244480a208 0x001c222488901441 0x01e0000000000000 0x003c000000000000

def z573 : W := mkw 0x00e97d2455d6a2a8 0x001d2fa48abad455 0xe1ffff3c7fffe3ff 0xfc3fffe78ffffc7f

def z574 : W := mkw 0x0040012000002200 0x0008002400000440 0xc000033000006380 0x1800006600000c70

def z575 : W := mkw 0x977403f45ea87ba8 0x92ee807e8bd50f75 0xfffc03fc7ff87fff 0xdfff807f8fff0fff

def z576 : W := mkw 0x977403f00ea87b00 0x92ee807e01d50f60 0xdfe003f00c007f82 0x1bfc007e01800ff0

def z577 : W := mkw 0x2e02a68a9b4754f0 0x45c054d15368ea9e 0xfe03ffffffc7ffff 0xffc07ffffff8ffff

def z578 : W := mkw 0x0000240001578001 0x00000480002af000 0x0000000000078000 0x000000000000f000

def z579 : W := mkw 0x640402dbb0085df0 0x4c80805b76010bbe 0xe00003fff0007ff8 0x1c00007ffe000fff

def z580 : W := mkw 0x91dd597560000002 0x323bab2eac000000 0xa1fcfcf3f0000005 0xb43f9f9e7e000000

def z581 : W := mkw 0x0000200081050450 0x400004001020a08a 0x0000000000078078 0x000000000000f00f

def z582 : W := mkw 0x91fd597564a82b02 0xb23fab2eac950560 0x01fc1c3070f80380 0x803f83860e1f0070

def z583 : W := mkw 0x400c6c51b15e0de0 0x08018d8a362bc1bc 0x201cfcc3f33e1c61 0x24039f987e67c38c

def z584 : W := mkw 0xb55403ff60000002 0x16aa807fec000000 0xbffc03fff0000007 0x97ff807ffe000000

def z585 : W := mkw 0x977403f00ea07200 0x92ee807e01d40e40 0x9ffc03f00c006007 0x93ff807e01800c00

def z586 : W := mkw 0x422c6c51bfff8de1 0x08458d8a37fff1bc 0xe01cfcf3ffff9fe5 0xfc039f9e7ffff3fc

def z587 : W := mkw 0x2e02a28a8b055450 0x45c054515160aa8a 0x1e03e3cf8f01fc1b 0x03c07c79f1e03f83

def z588 : W := mkw 0x0040012440002208 0x0008002488000441 0x0000030c00006018 0x0000006180000c03

def z589 : W := mkw 0x0802a00001050000 0x010054000020a000 0x0003e00000078000 0x20007c000000f000

def z590 : W := mkw 0x844403f000087b00 0x9088807e00010f60 0xc01c03f003f87f85 0xd803807e007f0ff0

def z591 : W := mkw 0xffdffffffb5f5df2 0x7ffbffffff6bebbe 0xffffffffffffffff 0xffffffffffffffff

def z592 : W := mkw 0x0008680001140000 0x00010d0000228000 0x001ce00003380001 0x00039c0000670000

def z593 : W := mkw 0x6e0eeedbbb5f5df0 0x4dc1dddb776bebbe 0xfe1cfcf3f3fe1fe5 0xffc39f9e7e7fc3fc

def z594 : W := mkw 0x91fd5d7574c2a2aa 0x323fabaeae985455 0x01fc1c3070c00380 0x803f83860e180070

def z595 : W := mkw 0xbdffdbff64a82b02 0xb7bffb7fec950560 0xbffffffff0f80387 0xb7fffffffe1f0070

def z596 : W := mkw 0x137001200ea02200 0x026e002401d40440 0xdffc03300ff86387 0xdbff806601ff0c70

def z597 : W := mkw 0x40002000811c0d40 0x08000400102381a8 0x0000000003381c00 0x0000000000670380

def z598 : W := mkw 0x7fbffedbbfffddf1 0x6ff7ffdb77fffbbe 0xffffffffffffffff 0xffffffffffffffff

def z599 : W := mkw 0x5b1ee851ab3d0d41 0x2b63dd0a3567a1a8 0x1e1ce0c383381c01 0x03c39c1870670380

def z600 : W := mkw 0xb9dfd97f60000002 0x373bfb2fec000000 0x21fffc3ff0000000 0xa43fff87fe000000

def z601 : W := mkw 0xbf7283aa0ea17210 0xd7ee507541d42e42 0x1fe3030c0c01e01a 0x03fc606181803c03

def z602 : W := mkw 0x2a02a00a8b055450 0x454054015160aa8a 0x6003e00f8f07fc78 0x6c007c01f1e0ff8f

def z603 : W := mkw 0x02e115245eeafba8 0x805c22a48bdd5f75 0xe1e31f3c7ffffffe 0xfc3c63e78fffffff

def z604 : W := mkw 0xbdd793fe40000002 0x37baf27fc8000000 0x9fff03fc00000007 0x93ffe07f80000000

def z605 : W := mkw 0x0a0280000a010000 0x0140500001402000 0x1e0300000c018002 0x03c0600001803000

def z606 : W := mkw 0x00e1152454c2a2a8 0x001c22a48a985455 0x01e31c307cc78386 0xe03c63860f98f070

def z607 : W := mkw 0xbfffdfff7eeafbaa 0xb7fffbffefdd5f75 0xffffffffffffffff 0xffffffffffffffff

def z608 : W := mkw 0x400c6851a11c0d40 0x08018d0a342381a8 0xc01ce0f383f81f85 0xd8039c1e707f03f0

def z609 : W := mkw 0x51bd5c5134fa89a1 0x2a37ab8a269f5134 0x01fc1c3070f80380 0x803f83860e1f0070

def z610 : W := mkw 0x0004005000000000 0x0000800a00000000 0x801c00f000000005 0x9003801e00000000

def z611 : W := mkw 0x1bbbd8000ea18001 0x23777b0001d43000 0x1ffffc000c018007 0xa3ffff8001803000

def z612 : W := mkw 0x0000000000000000 0x0000000000000000 0xc00000c003001c05 0x5800001800600380

def z613 : W := mkw 0x91fd5d7004faab01 0xb23fabae009f5560 0x01fc1c3000f80380 0x803f8386001f0070

def z614 : W := mkw 0x6e0aee8bbb5754f0 0x4dc15dd1776aea9e 0xfe03ffcfff07fc7f 0x7fc07ff9ffe0ff8f

def z615 : W := mkw 0x0040012440000000 0x0008002488000000 0xa000033c70000000 0x140000678e000000

def z616 : W := mkw 0x2883b40ed14784f8 0x45107681da28f09f 0x2003fc0ff0078078 0x24007f81fe00f00f

def z617 : W := mkw 0xbdffdbff6480a20a 0x37bffb7fec901441 0xbffffffffc01e01f 0xb7ffffffff803c03

def z618 : W := mkw 0x9ff793f00ea9fb01 0xb3fef27e01d53f60 0xdfff03f00ff9ff87 0xdbffe07e01ff3ff0

def z619 : W := mkw 0x000c485120000000 0x0001890a24000000 0x001c1c3070000000 0x800383860e000000

def z620 : W := mkw 0x0000000000000000 0x0000000000000000 0xc000003000c00384 0xd800000600180070

def z621 : W := mkw 0x1bfbfd244ff7a209 0x237f7fa489fef441 0x1fffff0c0fffe01f 0xe3ffffe181fffc03

def z622 : W := mkw 0x97f113a44ea0f208 0x92fe227489d41e41 0x1fe3030c0c01e01a 0x03fc606181803c03

def z623 : W := mkw 0x062002800ea87b00 0x80c4005001d50f60 0xde0003c00ff87f87 0x5bc0007801ff0ff0

def z624 : W := mkw 0x5bfffd75ffffafe9 0x2b7fffaebffff5fd 0xffffffffffffffff 0xffffffffffffffff

def z625 : W := mkw 0xfddffbffe11c0d42 0x3fbbff7ffc2381a8 0xbffffffff3381c07 0xb7fffffffe670380

def z626 : W := mkw 0x0081100440000000 0x0010220088000000 0x20031c0c70000000 0x240063818e000000

def z627 : W := mkw 0x3f1aea8a8b355451 0x67e35d515166aa8a 0x1e1ce0c383381c01 0x03c39c1870670380

def z628 : W := mkw 0x11b1100004a08001 0x2236220000941000 0x01e0000000000000 0x003c000000000000

def z629 : W := mkw 0xbf7683fa0ea97b10 0xd7eed07f41d52f62 0xdfff03fc0ff9ff9f 0xdbffe07f81ff3ff3

def z630 : W := mkw 0x00e1152454c2a2a8 0x001c22a48a985455 0x21e31f0c7c07e07a 0x243c63e18f80fc0f

def z631 : W := mkw 0x11f95d2454f2a2a9 0x223f2ba48a9e5455 0x01fc1c3070f80380 0x803f83860e1f0070

def z632 : W := mkw 0x2e02a28a8b055450 0x45c054515160aa8a 0xde00e3c38f007c07 0x5bc01c7871e00f80

def z633 : W := mkw 0x0000240001560000 0x00000480002ac000 0x0000000003fe0000 0x40000000007fc000

def z634 : W := mkw 0x022004001eeafba8 0x8044008003dd5f75 0x400000000ffffff8 0x4800000001ffffff

def z635 : W := mkw 0xbddfffff61560002 0x37bbffffec2ac000 0xbffffffff3fe0007 0xf7fffffffe7fc000

def z636 : W := mkw 0xff7eeffbbfff7ff0 0xdfefddff77ffeffe 0xffffffffffffffff 0xffffffffffffffff

def z637 : W := mkw 0xbf1eeadbab055452 0x77e3dd5b7560aa8a 0xfe1fe3cf8f07fc7f 0x7fc3fc79f1e0ff8f

def z638 : W := mkw 0x40002400915604e0 0x08000480122ac09c 0x0000000000060060 0x000000000000c00c

def z639 : W := mkw 0x40040051a0080d40 0x0800800a340101a8 0x000000c380001c00 0x0000001870000380

def z640 : W := mkw 0x19dbd92440000000 0x233b7b2488000000 0xbfffff3c70000007 0xb7ffffe78e000000

def z641 : W := mkw 0x022024008ff7d451 0x4044048011fefa8a 0x400000000ffffc78 0x4800000001ffff8f

def z642 : W := mkw 0x0000000000000000 0x0000000000000000 0x400000000c07e078 0x480000000180fc0f

def z643 : W := mkw 0x1bfbfd244ff78001 0x237f7fa489fef000 0xbfffff3c7fff8007 0xf7ffffe78ffff000

def z644 : W := mkw 0x00ed5d7574c2a2a8 0x001dabaeae985455 0xe1fffffffcc7e3ff 0xfc3fffffff98fc7f

def z645 : W := mkw 0x400c485120180900 0x0801890a24030120 0x001c000000380000 0x0003800000070000

def z646 : W := mkw 0x937401700ea87b00 0x926e802e01d50f60 0x41fc00300ff87f80 0xc83f800601ff0ff0

def z647 : W := mkw 0x2e02a28a8b055450 0x45c054515160aa8a 0x3e03e30f8c07e07a 0x27c07c61f180fc0f

def z648 : W := mkw 0xd7fd7ff5fffeffe8 0x9affaffebfffdffd 0xffffffffffffffff 0xffffffffffffffff

def z649 : W := mkw 0x19bbdc0004c28000 0x23377b8000985000 0x1ffffc000cc78007 0xe3ffff800198f000

def z650 : W := mkw 0x00084c0000520000 0x00010980000a4000 0x001c1c0000f80000 0x80038380001f0000

def z651 : W := mkw 0x977003a00ea07200 0x92ee007401d40e40 0xdfe003c00f007c07 0x5bfc007801e00f80

def z652 : W := mkw 0x2e02828a0a015010 0x45c0505141402a02 0xbe03e3cf8c01e01f 0x37c07c79f1803c03

def z653 : W := mkw 0x2e22a68a9fc7f6f8 0x45c454d153f8fedf 0xfe03e3cf8fc7ffff 0x7fc07c79f1f8ffff

def z654 : W := mkw 0x1b1aec000b770001 0x23635d80016ee000 0x1e1cfc0003fe0005 0xe3c39f80007fc000

def z655 : W := mkw 0x288bfc0a81578451 0x65117f81502af08a 0x2003fc0f80078078 0x24007f81f000f00f

def z656 : W := mkw 0x00c11524504200a0 0x001822a48a084014 0xe1e31f3c70c603e6 0xfc3c63e78e18c07c

def z657 : W := mkw 0x0000000000000000 0x0000000000000000 0x000300000c078006 0x600060000180f000

def z658 : W := mkw 0xa44403ff700022aa 0x1488807fee000455 0xe00003fff00063f8 0x1c00007ffe000c7f

def z659 : W := mkw 0x957403f004802200 0x12ae807e00900440 0xdffc03f00cc06387 0xdbff807e01980c70

def z660 : W := mkw 0x0000200081040440 0x0000040010208088 0x4000000003061c60 0x480000000060c38c

def z661 : W := mkw 0x2c0ecadb20000000 0x0581d95b64000000 0xbe1ffffff0000007 0xb7c3fffffe000000

def z662 : W := mkw 0x060022808b055450 0x40c004501160aa8a 0xde0003c00f07fc7f 0x5bc0007801e0ff8f

def z663 : W := mkw 0x0000000000000000 0x0000000000000000 0xa003030c00000006 0x3400606180000000

def z664 : W := mkw 0xdffffff1bfffffe1 0xbbfffffe37fffffc 0xfffffff3ffffffe7 0xfffffffe7ffffffc

def z665 : W := mkw 0x2c02828a00000000 0x0580505140000000 0x1e03030c00000002 0x03c0606180000000

def z666 : W := mkw 0x640c6edbb15e5df0 0x4c818ddb762bcbbe 0xe01cfffff3fe7ffd 0xfc039ffffe7fcfff

def z667 : W := mkw 0x975403f00a287b00 0x92ea807e01450f60 0xde1c03f003387f81 0x1bc3807e00670ff0

def z668 : W := mkw 0x40ed5d7574daaba8 0x081dabaeae9b5575 0xe1ff1f3c7cffe3fe 0xfc3fe3e78f9ffc7f

def z669 : W := mkw 0x022400500ea87b00 0x8044800a01d50f60 0xc01c00f00ff87f85 0xd803801e01ff0ff0

def z670 : W := mkw 0x00400124500022a8 0x000800248a000455 0xe003033c7c07e3fe 0x7c0060678f80fc7f

def z671 : W := mkw 0x2c02a28a81040440 0x0580545150208088 0xfe03e3cf83061c67 0x7fc07c79f060c38c

def z672 : W := mkw 0x00cd597560000000 0x0019ab2eac000000 0xa1fffffff0000007 0xb43ffffffe000000

def z673 : W := mkw 0x91fd5d7564f28003 0x323fabaeac9e5000 0x01fc1c3070f80000 0x803f83860e1f0000

def z674 : W := mkw 0x060002800a005000 0x00c0005001400a00 0x1e0003000c006002 0x03c0006001800c00

def z675 : W := mkw 0x9ffbffa00ff7f201 0xb3ff7ff401fefe40 0x1fffff000fffe007 0xe3ffffe001fffc00

def z676 : W := mkw 0x40cd7d75f15e0de0 0x0819afaebe2bc1bc 0xe1fffffff3fe1fe7 0xfc3ffffffe7fc3fc

def z677 : W := mkw 0x0000000080000440 0x0000000010000088 0xe00000c380001c60 0x1c0000187000038c

def z678 : W := mkw 0xae46a3ffeb055452 0x55c8d47ffd60aa8a 0xfe03e3ffff07fc7f 0x7fc07c7fffe0ff8f

def z679 : W := mkw 0x0a22a4000ff78001 0x0144548001fef000 0x1e03e0000fff8007 0x63c07c0001fff000

def z680 : W := mkw 0x00811404504280a8 0x001022808a085015 0xe0031c3c70c783fc 0xfc0063878e18f07f

def z681 : W := mkw 0x2400028a00005010 0x4480005140000a02 0x0000030c00006018 0x0000006180000c03

def z682 : W := mkw 0xbf1eeadb2b350003 0x37e3dd5b6566a000 0x1e1ce0c383380001 0x03c39c1870670000

def z683 : W := mkw 0x9bfffd700fffab01 0xb37fffae01fff560 0x1ffffc300fff8387 0xe3ffff8601fff070

def z684 : W := mkw 0x0000000000000000 0x0000000000000000 0xa0001c3070000004 0xb40003860e000000

def z685 : W := mkw 0x5bbffc51afff8d41 0x2b77ff8a35fff1a8 0x1ffffcc38fff9c07 0xe3ffff9871fff380

def z686 : W := mkw 0x0020000004802200 0x0004000000900440 0x400000000cc06380 0x4800000001980c70

def z687 : W := mkw 0x00e1152454c2a2a8 0x001c22a48a985455 0x01e31f3c7cc1e39a 0x803c63e78f983c73

def z688 : W := mkw 0x00042050810c0d40 0x0000840a102181a8 0xe01ce0f383fe1fe5 0xfc039c1e707fc3fc

def z689 : W := mkw 0x00811404504280a8 0x001022808a085015 0x00001c0070000000 0x000003800e000000

def z690 : W := mkw 0x2400228a81045450 0x4480045150208a8a 0xe000e3cf83067c7d 0x7c001c79f060cf8f

def z691 : W := mkw 0x2600028a8a005450 0x44c0005151400a8a 0xfe0003cf8f007c7f 0x5fc00079f1e00f8f

def z692 : W := mkw 0x6e02a68a9b5f5df0 0x4dc054d1536bebbe 0xfe03e3cf8fffffff 0x7fc07c79f1ffffff

def z693 : W := mkw 0x0060012004802200 0x000c002400900440 0x01e0003000c00380 0x803c000600180070

def z694 : W := mkw 0x97f513f44ea87b00 0x92fea27e89d50f60 0xffff1ffc7ff87f87 0xffffe3ff8fff0ff0

def z695 : W := mkw 0xbf16a2da8b2d5d50 0xd7e2d45b5165abaa 0x1e1ce0c383381c01 0x03c39c1870670380

def z696 : W := mkw 0x2e02a28a0b055010 0x45c054514160aa02 0x1e03e30c0f07e01f 0x63c07c6181e0fc03

def z697 : W := mkw 0xbddbdbae40000002 0x37bb7b75c8000000 0x1fffff0c00000007 0xa3ffffe180000000

def z698 : W := mkw 0x1bbbfc000ff78001 0x23777f8001fef000 0x1fe3fc000c078002 0x23fc7f800180f000

def z699 : W := mkw 0xbdffdfff64f28003 0x37bffbffec9e5000 0xbffffffff0f80007 0xb7fffffffe1f0000

def z700 : W := mkw 0x2e83b68edb47d4f8 0x45d076d1db68fa9f 0xfe03ffcfff07fc7f 0x7fc07ff9ffe0ff8f

def z701 : W := mkw 0x9154017000000000 0x122a802e00000000 0x01fc003000000000 0x803f800600000000

def z702 : W := mkw 0xd77427f09ffe7fe0 0x9aee84fe13ffcffc 0xdffc03f00ffe7fe7 0xdbff807e01ffcffc

def z703 : W := mkw 0xfd1eeedbb15e0de2 0x3fa3dddb762bc1bc 0xfe1cfcf3f3fe1fe5 0xffc39f9e7e7fc3fc

def z704 : W := mkw 0xbfd3b3aecb055452 0x77fa7675d960aa8a 0xffe3e3cf8f07fc7f 0x7ffc7c79f1e0ff8f

def z705 : W := mkw 0x0081140000428000 0x0010228000085000 0x00031c0000078000 0x200063800000f000

def z706 : W := mkw 0x2e02a28a8b055450 0x45c054515160aa8a 0x3e03e0cf83079c79 0x27c07c19f060f38f

def z707 : W := mkw 0x422024009fdffff8 0x4844048013fbffff 0x400000000ffffff8 0x4800000001ffffff

def z708 : W := mkw 0xc44403f5f0087fe8 0x9888807ebe010ffd 0xe00003fff0007ff8 0x1c00007ffe000fff

def z709 : W := mkw 0x422024009ffeffe8 0x8844048013ffdffd 0x400000000ffffff8 0x4800000001ffffff

def z710 : W := mkw 0x51fd5d7574faaba9 0x2a3fabaeae9f5575 0x01fc1c3070f80380 0x803f83860e1f0070

def z711 : W := mkw 0x35b95e8a84f2d451 0x66b72bd1509e5a8a 0xe1fc1fcf80f87c78 0x9c3f83f9f01f0f8f

def z712 : W := mkw 0xbddfdbff60080902 0x37bbfb7fec010120 0xbffffffff0f80387 0xb7fffffffe1f0070

def z713 : W := mkw 0x40ed7975e59caf48 0x081daf2ebcb395e9 0x01ffe3cf8f39fc1b 0x003ffc79f1e73f83

def z714 : W := mkw 0x1bbbfc000ff78001 0x23777f8001fef000 0xdffffc300fff8387 0xfbffff8601fff070

def z715 : W := mkw 0x93dd7975eb055452 0x727baf2ebd60aa8a 0x41fc1c307f07fc78 0xc83f83860fe0ff8f

def z716 : W := mkw 0x133024000ff60000 0x0266048001fec000 0x1ffc00000ffe0007 0xc3ff800001ffc000

def z717 : W := mkw 0x977403f00ea87b00 0x92ee807e01d50f60 0xdffc03f00fffffff 0xdbff807e01ffffff

def z718 : W := mkw 0x1b3ae8000fb50001 0x23675d0001f6a000 0x1fffe0000fff8007 0xe3fffc0001fff000

def z719 : W := mkw 0x2aabd80f6ea87b02 0xa5557b01edd50f60 0x6003fc0ffff87f80 0x6c007f81ffff0ff0

def z720 : W := mkw 0x937401700ea87b00 0x926e802e01d50f60 0x5ffc00300ff87f87 0xcbff800601ff0ff0

def z721 : W := mkw 0x400c6c51b15e0de0 0x08018d8a362bc1bc 0xe01cfff3fffe7fe7 0xfc039ffe7fffcffc

def z722 : W := mkw 0x844403f450087ba8 0x9088807e8a010f75 0xc00003f070007f80 0x1800007e0e000ff0

def z723 : W := mkw 0xfdd3b7aed15e0de2 0x3fba76f5da2bc1bc 0x5fe3030c03fe1fe2 0x4bfc6061807fc3fc

def z724 : W := mkw 0xbddfdbff60080902 0x37bbfb7fec010120 0xfffffffff0001f87 0xbffffffffe0003f0

def z725 : W := mkw 0x133020000fa40000 0x0266040001f48000 0x1ffce0000ffe0007 0xe3ff9c0001ffc000

def z726 : W := mkw 0x11b95c0004f28001 0x22372b80009e5000 0x1ffc1c0000f80007 0x83ff8380001f0000

def z727 : W := mkw 0x3ff393ae4ea1f219 0x67fe7275c9d43e43 0x1fe3030c0c01e01a 0x03fc606181803c03

def z728 : W := mkw 0x00e1152454c2a2a8 0x001c22a48a985455 0xe1ff1f3c7fffe3ff 0xfc3fe3e78ffffc7f

def z729 : W := mkw 0x1b5ae9245b3522a9 0x236b5d248b66a455 0xfe1ce33c733863f9 0x1fc39c678e670c7f

def z730 : W := mkw 0x2c02828a80005450 0x4580505150000a8a 0xfe03e3cf8c07fc7f 0x7fc07c79f180ff8f

def z731 : W := mkw 0xbddfdbff60000002 0x37bbfb7fec000000 0xbffffffff3f80007 0xf7fffffffe7f0000

def z732 : W := mkw 0x844403f080087f50 0xd088807e10010fea 0xc00003f000007ff8 0x1800007e00000fff

def z733 : W := mkw 0x844407f0104a7ba0 0x908880fe02094f74 0xe0001ff070c67fe4 0xfc0003fe0e18cffc

def z734 : W := mkw 0x2e02a28a8b055450 0x45c054515160aa8a 0xfe1fe3cf8ffffc7f 0xffc3fc79f1ffff8f

def z735 : W := mkw 0x977403f00ea9fb01 0x92ee807e01d53f60 0xdffc03f00ff9ff87 0xdbff807e01ff3ff0

def z736 : W := mkw 0xa44403ff60085902 0x9488807fec010b20 0xa00003fff0001c00 0x1400007ffe000380

def z737 : W := mkw 0xbddfdbff60000002 0x37bbfb7fec000000 0xbffcfffff0000001 0x97ff9ffffe000000

def z738 : W := mkw 0x977403f00ea87b00 0x92ee807e01d50f60 0xdffc00f003f81f85 0xdbff801e007f03f0

def z739 : W := mkw 0x844403f000080900 0x1088807e00010120 0xc00003f000001f80 0x1800007e000003f0

def z740 : W := mkw 0xff1eeadbab1d5d52 0x7fe3dd5b7563abaa 0x1e1ce0c383381c01 0x03c39c1870670380

def z741 : W := mkw 0x2e02a28a8b055450 0x45c054515160aa8a 0x3e03e3cf8f07fc7b 0x27c07c79f1e0ff8f

def z742 : W := mkw 0x13b114045ee280a8 0x027622808bdc5015 0x3fff1c0c7fff807f 0xe7ffe3818ffff00f

def z743 : W := mkw 0x977403f00ea87b00 0x92ee807e01d50f60 0xfffce3f38ff87f87 0xffff9c7e71ff0ff0

def z744 : W := mkw 0x133000000ea18001 0x0266000001d43000 0x1ffc00000ff98007 0xc3ff800001ff3000

def z745 : W := mkw 0x977403f12ea87b00 0x92ee807e25d50f60 0xfffc03f3fff87f87 0xdfff807e7fff0ff0

def z746 : W := mkw 0xbddfdbff60000002 0x37bbfb7fec000000 0xfffffffff3001c07 0xfffffffffe600380

def z747 : W := mkw 0x6e0ecedb3a5b59b0 0x4dc1d9db674b6b36 0x1e1f1f3c7cf9e39a 0x83c3e3e78f9f3c73

def z748 : W := mkw 0xa44403ff60082b02 0x9488807fec010560 0xa00003fff0000380 0x1400007ffe000070

def z749 : W := mkw 0x133868000fb40000 0x02670d0001f68000 0x1ffce0000ff80007 0xc3ff9c0001ff0000

def z750 : W := mkw 0x688bfc0ff15684ea 0x2d117f81fe2ad09d 0x2003fc0ff0078078 0x24007f81fe00f00f

def z751 : W := mkw 0x173402d00ea85900 0x02e6805a01d50b20 0xdffc03f00ff87f87 0xdbff807e01ff0ff0

def z752 : W := mkw 0x2e02a28a8b055450 0x45c054515160aa8a 0xfe03e3cf8c07fc7a 0x3fc07c79f180ff8f

def z753 : W := mkw 0x1110000000000000 0x0222000000000000 0x1ffc000003f80007 0xc3ff8000007f0000

def z754 : W := mkw 0x400c6c51b15f8de1 0x08018d8a362bf1bc 0xe01cfcf3f3ff9fe5 0xfc039f9e7e7ff3fc

def z755 : W := mkw 0x1b9bf8000b350001 0x23737f000166a000 0x1ffcfc0003380001 0x83ff9f8000670000

def z756 : W := mkw 0xb976a17a85ad2f50 0xd72ed42f50b5a5ea 0x21ffe03f80ff83f8 0xa43ffc07f01ff07f

def z757 : W := mkw 0x1bbbfc008ff78451 0x63777f8011fef08a 0x1ffffc000fff807f 0xe3ffff8001fff00f

def z758 : W := mkw 0x1bbbfc000ff78001 0x23777f8001fef000 0xfffffc000fff8067 0xffffff8001fff00c

def z759 : W := mkw 0x864423f08b0d7f50 0xd0c8847e1161afea 0xc00003f00f07fff8 0x5800007e01e0ffff

def z760 : W := mkw 0x199bd80000300001 0x23337b0000060000 0x1ffffc0000380007 0xa3ffff8000070000

def z761 : W := mkw 0xbff393ae4ea1f203 0xb7fe7275c9d43e40 0x1fe3030c0c01e002 0x03fc606181803c00

def z762 : W := mkw 0x1bbbfc045ff780a9 0x23777f808bfef015 0xfffffc3c7fff83ff 0xffffff878ffff07f

def z763 : W := mkw 0x1bbbfc000ff78001 0x23777f8001fef000 0x5ffffc000fffe07f 0xebffff8001fffc0f

def z764 : W := mkw 0x2ccbdbaf60000002 0x25997b75ec000000 0xbfe3fffff0000007 0xb7fc7ffffe000000

def z765 : W := mkw 0x864403f00a087b00 0x90c8807e01410f60 0xc00003f00f007f80 0x5800007e01e00ff0

def z766 : W := mkw 0xbddfdbff60000002 0x37bbfb7fec000000 0xbfe3fffff0000002 0x37fc7ffffe000000

def z767 : W := mkw 0xbddfdbff60000002 0x37bbfb7fec000000 0x3fffff3ff0000002 0xa7ffffe7fe000000

def z768 : W := mkw 0x00e1152454c2a2a8 0x001c22a48a985455 0xe1e3fffffcc7e3ff 0xfc3c7fffff98fc7f

def z769 : W := mkw 0x1b3ac8000ea00000 0x2367590001d40000 0x1ffce0000ff80007 0xc3ff9c0001ff0000

def z770 : W := mkw 0x844403f560087b02 0x9088807eac010f60 0xc00003f070007f80 0x1800007e0e000ff0

def z771 : W := mkw 0x400c6c51b15e0de0 0x08018d8a362bc1bc 0x401cfcf3f3fe1fe1 0xc8039f9e7e7fc3fc

def z772 : W := mkw 0x13b95c000ef28001 0x22772b8001de5000 0x1fff1c000fff8007 0xe3ffe38001fff000

def z773 : W := mkw 0x977003a00ea87b00 0x92ee007401d50f60 0x5ffc03000ff87f87 0xcbff806001ff0ff0

def z774 : W := mkw 0x39dbd92f60000002 0x273b7b25ec000000 0xbfffff3ff0000007 0xb7ffffe7fe000000

def z775 : W := mkw 0x1b9bfc000b570000 0x23737f80016ae000 0x1ffffc000fff8007 0xe3ffff8001fff000

def z776 : W := mkw 0xbff393ae4ea1f218 0xd7fe7275c9d43e43 0x1fe3030c0c01e01a 0x03fc606181803c03

def z777 : W := mkw 0xbd3ecedb34c2a2aa 0x37a7d9db66985455 0x5e1ce0c38cc7e3f9 0x4bc39c187198fc7f

def z778 : W := mkw 0x5bb79051bea98de1 0x2b76f20a37d531bc 0xffe300f3fc019fe2 0x1ffc601e7f8033fc

def z779 : W := mkw 0xfddfdbff60180902 0x3fbbfb7fec030120 0xbffffffff0380007 0xb7fffffffe070000

def z780 : W := mkw 0x199bd80000000000 0x23337b0000000000 0x1ffffc0003f80007 0xe3ffff80007f0000

def z781 : W := mkw 0xbd9fdadb20000002 0x37b3fb5b64000000 0xbffffcf3f0000007 0xb7ffff9e7e000000

def z782 : W := mkw 0x02c13124cb055450 0x405826249960aa8a 0xe1e31f3c7f07fc7e 0xfc3c63e78fe0ff8f

def z783 : W := mkw 0xbddfdbff60007202 0xb7bbfb7fec000e40 0xbffffffff0006007 0xb7fffffffe000c00

def z784 : W := mkw 0xe44403ff700809a2 0x1c88807fee010134 0xa00003fff0000380 0x1400007ffe000070

def z785 : W := mkw 0x844403f000087b00 0x9088807e00010f60 0x000000f000001f80 0x0000001e000003f0

def z786 : W := mkw 0x133004000ee20000 0x0266008001dc4000 0x1ffc1c000ffe0007 0xe3ff838001ffc000

def z787 : W := mkw 0x5bbbfc05fff784e9 0x2b777f80bffef09d 0x3ffffc0fffff807f 0xe7ffff81fffff00f

def z788 : W := mkw 0x133000000ea02200 0x0266000001d40440 0x5ffc00000ff86387 0xcbff800001ff0c70

def z789 : W := mkw 0xd1fd5d7574faaba8 0x9a3fabaeae9f5575 0x01fc1c3070f80380 0x803f83860e1f0070

def z790 : W := mkw 0xbf1eeadbab2d5d52 0xf7e3dd5b7565abaa 0x1e1ce0c383381c01 0x03c39c1870670380

def z791 : W := mkw 0x644403fff0087ff8 0x4c88807ffe010fff 0xe00003fff0007ff8 0x1c00007ffe000fff

def z792 : W := mkw 0xff1eeadbab3d5d50 0xdfe3dd5b7567abaa 0x1e1ce0c383381c01 0x03c39c1870670380

def z793 : W := mkw 0x1bbbfc000ff78001 0x23777f8001fef000 0x1ffffc000f3f8003 0x23ffff8001e7f000

def z794 : W := mkw 0xb77403fa0ea87b10 0xd6ee807f41d50f62 0xdffc03fc0ff87f9f 0xdbff807f81ff0ff3

def z795 : W := mkw 0x022024009ff7f6f9 0x4044048013fefedf 0x400000000ffffff8 0x4800000001ffffff

def z796 : W := mkw 0x53386c01bff604e0 0x0a670d8037fec09c 0x3ffcfc03fffe0067 0xe7ff9f807fffc00c

def z797 : W := mkw 0x13b97c000ff68001 0x22772f8001fed000 0x1ffcfc000ffe0007 0xe3ff9f8001ffc000

def z798 : W := mkw 0xa44403ff60080902 0x1488807fec010120 0xe00003fff0001f80 0x1c00007ffe0003f0

def z799 : W := mkw 0x1bbbfc000ff7f201 0xa3777f8001fefe40 0x1ffffc000fffe007 0xe3ffff8001fffc00

def z800 : W := mkw 0x973402d00ea87b00 0x92e6805a01d50f60 0x5ffc00c00ff87f87 0xcbff801801ff0ff0

def z801 : W := mkw 0x13b110000ea08000 0x0276220001d41000 0x1fff00000ff98007 0xc3ffe00001ff3000

def z802 : W := mkw 0xacc793ff60000002 0x1598f27fec000000 0xbfe3fffff0000007 0xb7fc7ffffe000000

def z803 : W := mkw 0x19bbd80004a00000 0x23377b0000940000 0x1ffffc0000f80007 0xa3ffff80001f0000

def z804 : W := mkw 0x1b3aec000ff70001 0x23675d8001fee000 0x1ffcfc000ffe0007 0xe3ff9f8001ffc000

def z805 : W := mkw 0x422024009ffe0de0 0x0844048013ffc1bc 0x400000000ffe1fe0 0x4800000001ffc3fc

def z806 : W := mkw 0xbddfdbff60085902 0xb7bbfb7fec010b20 0xbffffffff0001c07 0xb7fffffffe000380

def z807 : W := mkw 0x0aabfc000fd78000 0x01557f8001faf000 0x1ffffc000fff8007 0xe3ffff8001fff000

def z808 : W := mkw 0xbd5ecbfb20000000 0x17abd97f64000000 0xbffffffff0000007 0xb7fffffffe000000

def z809 : W := mkw 0x1b3280000ea10000 0x0366500001d42000 0x1fff00000ff98007 0xc3ffe00001ff3000

def z810 : W := mkw 0xd55427f0915e0de0 0x1aaa84fe122bc1bc 0xdffc03f003fe1fe7 0xdbff807e007fc3fc

def z811 : W := mkw 0x977403f00ea87b00 0x92ee807e01d50f60 0xfffc03f00ffe7fe7 0xffff807e01ffcffc

def z812 : W := mkw 0xbddfdbff60018003 0x37bbfb7fec003000 0xbffffffff0018007 0xb7fffffffe003000

def z813 : W := mkw 0x422024009fffafe9 0x0844048013fff5fd 0x400000000ffffff8 0x4800000001ffffff

def z814 : W := mkw 0xbddfdbff60000002 0x37bbfb7fec000000 0x9ffcfff3f0000007 0x93ff9ffe7e000000

def z815 : W := mkw 0x3bbbfc0a8ff78451 0x67777f8151fef08a 0x1ffffc038fff8007 0xe3ffff8071fff000

def z816 : W := mkw 0x3d9fdadb20000000 0x27b3fb5b64000000 0xbffffffff0000007 0xb7fffffffe000000

def z817 : W := mkw 0x1bbbfc008ff78441 0x23777f8011fef088 0x5ffffc000fff9c67 0xebffff8001fff38c

def z818 : W := mkw 0xa66427ff6ff78003 0x14cc84ffedfef000 0xa00003ffffff8000 0x5400007ffffff000

def z819 : W := mkw 0x133848000ea00000 0x0267090001d40000 0x1ffcfc000ff80007 0xe3ff9f8001ff0000

def z820 : W := mkw 0xbddbdbaf60000002 0x37bb7b75ec000000 0xbfe3ff3ff0000006 0xb7fc7fe7fe000000

def z821 : W := mkw 0x133020008fa55450 0x4266040011f4aa8a 0x5ffc00000ffffc7f 0xcbff800001ffff8f

def z822 : W := mkw 0x133000000ea00000 0x0266000001d40000 0x1ffc000003f80001 0x83ff8000007f0000

def z823 : W := mkw 0x1bbbfc001ff780a1 0x23777f8003fef014 0x1ffffc307fff8387 0xe3ffff860ffff070

def z824 : W := mkw 0xb77403fe4ea87b02 0x96ee807fc9d50f60 0xdffc03fc0ff87f87 0xdbff807f81ff0ff0

def z825 : W := mkw 0x2e02a28a8b355451 0x45c054515166aa8a 0xfe03e3cf8f3ffc7f 0x7fc07c79f1e7ff8f

def z826 : W := mkw 0x1bbbf8000fb58001 0x23777f0001f6b000 0x1fffe0000ff98007 0xc3fffc0001ff3000

def z827 : W := mkw 0x7f1eeadbab3d5d51 0x6fe3dd5b7567abaa 0x1e1ce0c383381c01 0x03c39c1870670380

def z828 : W := mkw 0x8ccffff0015ffb01 0xb199fffe002bff60 0xc003fff00007ff80 0x38007ffe0000fff0

def z829 : W := mkw 0x1b9bd8000a200000 0x23737b0001440000 0x1ffffc0003380007 0xa3ffff8000670000

def z830 : W := mkw 0x488bfc01b15604e0 0x29117f80362ac09c 0x2003fc03f0060060 0x24007f807e00c00c

def z831 : W := mkw 0x000c6c51215e0900 0x00018d8a242bc120 0xe01cfcf3f3fe1f85 0xfc039f9e7e7fc3f0

def z832 : W := mkw 0x844403f000082b00 0x9088807e00010560 0x800003f000000380 0x1000007e00000070

def z833 : W := mkw 0x5bbbfc01aff78441 0x2b777f8035fef088 0x1ffffc038fff8007 0xe3ffff8071fff000

def z834 : W := mkw 0x977403f00ea97b10 0xd2ee807e01d52f62 0xdffc03f00ff9ff9f 0xdbff807e01ff3ff3

def z835 : W := mkw 0xbddbdbaf60000002 0x37bb7b75ec000000 0x3fffff0ff0000007 0xa7ffffe1fe000000

def z836 : W := mkw 0xe44403fff0087fe2 0x9c88807ffe010ffc 0xe00003fff0007fe0 0x1c00007ffe000ffc

def z837 : W := mkw 0x866403f00ea87b00 0x90cc807e01d50f60 0xc00003f00c007f80 0x1800007e01800ff0

def z838 : W := mkw 0x1bbbfc000ff78001 0x23777f8001fef000 0xbfffff0c0fff8007 0xf7ffffe181fff000

def z839 : W := mkw 0x1b32a0000fa50000 0x0366540001f4a000 0x1ffce0000ff80007 0xc3ff9c0001ff0000

def z840 : W := mkw 0xaccfdbff60087b02 0xb599fb7fec010f60 0xe003fffff0007f80 0x3c007ffffe000ff0

def z841 : W := mkw 0x13b134000ff78001 0x0276268001fef000 0x1fff1c000fff8007 0xe3ffe38001fff000

def z842 : W := mkw 0x1bbbfc000ff78001 0x23777f8001fef000 0x1fffff0c0fffe01f 0xe3ffffe181fffc03

def z843 : W := mkw 0x2ee3b7aedfc7f6f8 0x45dc76f5dbf8fedf 0x1fe0fcf3f3c01f81 0x83fc1f9e7e7803f0

def z844 : W := mkw 0x1b3ae8000fb50001 0x23675d0001f6a000 0x1ffce00003f80001 0x83ff9c00007f0000

def z845 : W := mkw 0x400c6c51b15e0de0 0x08018d8a362bc1bc 0xc01cfcf3f3f81f85 0xd8039f9e7e7f03f0

def z846 : W := mkw 0x1bbbfc000ff78001 0x23777f8001fef000 0x3ffffc0c0fff807f 0xe7ffff8181fff00f

def z847 : W := mkw 0x400c6c51b15f0df0 0x48018d8a362be1be 0xe01cfcf3f3ff9ffd 0xfc039f9e7e7ff3ff

def z848 : W := mkw 0x844423f0810c7f40 0x9088847e10218fe8 0xe000e3f383067fe5 0x7c001c7e7060cffc

def z849 : W := mkw 0x977403f00ea87b00 0x92ee807e01d50f60 0xdfff03f00fffff87 0xfbffe07e01fffff0

def z850 : W := mkw 0x5bbbfc013ff780a1 0x2b777f8027fef014 0x1ffffc007fff8007 0xe3ffff800ffff000

def z851 : W := mkw 0x133000000ea00000 0x0266000001d40000 0xffff030c0fffe07f 0xffffe06181fffc0f

def z852 : W := mkw 0x400c6851a11c0d40 0x08018d0a342381a8 0xe01cfcf3f3f81f85 0xfc039f9e7e7f03f0

def z853 : W := mkw 0x400c4c51305a09a0 0x0801898a260b4134 0xe01cfcf3f3f81f85 0xfc039f9e7e7f03f0

def z854 : W := mkw 0xbddfdbff60300003 0x37bbfb7fec060000 0xbffffffff0380007 0xb7fffffffe070000

def z855 : W := mkw 0x1bbbfc008ff7d451 0x63777f8011fefa8a 0x1ffffc000fff9c07 0xe3ffff8001fff380

def z856 : W := mkw 0xd1fd5d7574daabaa 0x3a3fabaeae9b5575 0x01fc1c3070f80380 0x803f83860e1f0070

def z857 : W := mkw 0x977403f00ea87b00 0x92ee807e01d50f60 0xfffc1ff07ff87f87 0xffff83fe0fff0ff0

def z858 : W := mkw 0x1114005000080900 0x0222800a00010120 0xdffc00f003f81f87 0xdbff801e007f03f0

def z859 : W := mkw 0xa44403fe40087b02 0x9488807fc8010f60 0xc00003fc00007f80 0x1800007f80000ff0

def z860 : W := mkw 0x1bb394000ee38001 0x2376728001dc7000 0x1fff1c000fff8007 0xe3ffe38001fff000

def z861 : W := mkw 0x00c11524504200a0 0x001822a48a084014 0xe1e31f3c7cc7e3fe 0xfc3c63e78f98fc7f

def z862 : W := mkw 0xbddfdbff60000002 0x37bbfb7fec000000 0x1ffffffff0000003 0x83fffffffe000000

def z863 : W := mkw 0x2c02a28a81040440 0x0580545150208088 0xfe03e3cf8f07fc7f 0x7fc07c79f1e0ff8f

def z864 : W := mkw 0xbff393ae4ea17212 0xf7fe7275c9d42e42 0x1fe3030c0c01e01a 0x03fc606181803c03

def z865 : W := mkw 0x488bfc05f15784e9 0x29117f80be2af09d 0x2003fc0ff0078078 0x24007f81fe00f00f

def z866 : W := mkw 0xbddfdbff60000002 0x37bbfb7fec000000 0xfffffffff0c00387 0xfffffffffe180070

def z867 : W := mkw 0x846407f014cafba8 0x908c80fe02995f75 0xc00003f00cc7fff8 0x5800007e0198ffff

def z868 : W := mkw 0x1bbbfc012ff78001 0x23777f8025fef000 0x3ffffc03ffff8007 0xe7ffff807ffff000

def z869 : W := mkw 0xb55c4bff60000002 0x16ab897fec000000 0xbffcfffff0000007 0xb7ff9ffffe000000

def z870 : W := mkw 0x133000000ea00000 0x0266000001d40000 0xdffc00c00ff81c07 0xdbff801801ff0380

def z871 : W := mkw 0x977403f00ea87b00 0x92ee807e01d50f60 0x5ffc03300ff87f82 0xcbff806601ff0ff0

def z872 : W := mkw 0x1bbbfc000ff60000 0x23777f8001fec000 0x1ffffc000ffe0007 0xe3ffff8001ffc000

def z873 : W := mkw 0x2e02a28a8b055450 0x45c054515160aa8a 0xfe03e3ff8fc7ffff 0xffc07c7ff1f8ffff

def z874 : W := mkw 0xe44403fff0085df2 0x5c88807ffe010bbe 0xe00003fff0007ff8 0x1c00007ffe000fff

def z875 : W := mkw 0xbdd393ae40000002 0x37ba7275c8000000 0xbfe3fffff0000007 0xb7fc7ffffe000000

def z876 : W := mkw 0x977403f00ea87b00 0x92ee807e01d50f60 0x5ffc03c00ff87f83 0x4bff807801ff0ff0

def z877 : W := mkw 0x844403f000085900 0x9088807e00010b20 0x800003f000001c00 0x1000007e00000380

def z878 : W := mkw 0x1bbbfc000ff78001 0x23777f8001fef000 0xdfffff000fffe007 0xfbffffe001fffc00

def z879 : W := mkw 0x1bbbdc000ef38001 0x23777b8001de7000 0x1fff1c000cff8006 0xe3ffe380019ff000

def z880 : W := mkw 0x1bbbdc000ef38001 0x23777b8001de7000 0x1ffc1c0000f80000 0x83ff8380001f0000

def z881 : W := mkw 0xbddfdbff60087b02 0xb7bbfb7fec010f60 0xfffffffff3f87f87 0xfffffffffe7f0ff0

def z882 : W := mkw 0xd7786fa1bff676e0 0x9aef0df437fecedc 0x3fe0ff03fc066062 0x27fc1fe07f80cc0c

def z883 : W := mkw 0x1b9bf8000b350001 0x23737f000166a000 0x1fffe00003380003 0x03fffc0000670000

def z884 : W := mkw 0x400c6c51b15e0de0 0x08018d8a362bc1bc 0x001cfcf3f3fe1f85 0xe0039f9e7e7fc3f0

def z885 : W := mkw 0xbddfdbff60000002 0x37bbfb7fec000000 0xbffffffffc01e01f 0xb7ffffffff803c03

def z886 : W := mkw 0x3bbbfc0b2ff78003 0x27777f8165fef000 0x1ffffc038fff8007 0xe3ffff8071fff000

def z887 : W := mkw 0x133000000ea80900 0x0266000001d50120 0x5ffc00000ff81f87 0xcbff800001ff03f0

def z888 : W := mkw 0x199bf80001140000 0x23337f0000228000 0x1ffffc0003380007 0xa3ffff8000670000

def z889 : W := mkw 0x2e02828a0a005000 0x05c0505141400a00 0xfe03e3cf8f07fc7f 0x7fc07c79f1e0ff8f

def z890 : W := mkw 0x977403f00ea87b00 0x92ee807e01d50f60 0x5ffc00f00ff87f81 0xcbff801e01ff0ff0

def z891 : W := mkw 0x84c517f4504afba8 0x9098a2fe8a095f75 0xe0031ffc7007fff8 0x3c0063ff8e00ffff

def z892 : W := mkw 0x1bbbdc000ef38001 0x23777b8001de7000 0x1fff1c000ff98007 0xc3ffe38001ff3000

def z893 : W := mkw 0x422024009ff784e1 0x0844048013fef09c 0x000000000fff8060 0x4000000001fff00c

def z894 : W := mkw 0x133000000ea00000 0x0266000001d40000 0xdffc00300ff80387 0xdbff800601ff0070

def z895 : W := mkw 0x400c6c51b15e0de0 0x08018d8a362bc1bc 0xe01ffcfff3ff9ffd 0xfc03ff9ffe7ff3ff

def z896 : W := mkw 0x1bbbfc044ff78001 0x23777f8089fef000 0x3ffffc0c7fff8007 0xe7ffff818ffff000

def z897 : W := mkw 0x979516d45a6ad9a8 0x92f2a2da8b4d5b35 0x3e1f1ccc733f9c79 0x27c3e3998e67f38f

def z898 : W := mkw 0x3bbbfc0feff78453 0x67777f81fdfef08a 0x3ffffc0fffff807f 0xe7ffff81fffff00f

def z899 : W := mkw 0x13b114000ee28000 0x0276228001dc5000 0x1ffc1c000ff80007 0xc3ff838001ff0000

def z900 : W := mkw 0x1b3280000ea00000 0x0366500001d40000 0x1fffe0000ff80007 0xe3fffc0001ff0000

def z901 : W := mkw 0x1bbbd8000ea18001 0x23777b0001d43000 0x1ffffc000ff98007 0xe3ffff8001ff3000

def z902 : W := mkw 0x977403f00ea8fb08 0x92ee807e01d51f61 0xdffc03f00ff9ff9f 0xdbff807e01ff3ff3

def z903 : W := mkw 0xbddfdbff60005012 0x77bbfb7fec000a02 0xbffffffff000601f 0xb7fffffffe000c03

def z904 : W := mkw 0x1bbbfc000ff78001 0x23777f8001fef000 0x1fff1c000fff8002 0xc3ffe38001fff000

def z905 : W := mkw 0x1bbbdc000ef38001 0x23777b8001de7000 0x1ffffc000cf98007 0xa3ffff80019f3000

def z906 : W := mkw 0x688bfc0ff15784f8 0x4d117f81fe2af09f 0x2003fc0ff0078078 0x24007f81fe00f00f

def z907 : W := mkw 0x13b95c000ef28001 0x22772b8001de5000 0x1ffc1c0003f80001 0x83ff8380007f0000

def z908 : W := mkw 0x844403f000087b00 0x9088807e00010f60 0xe00003fc00007ff8 0x1c00007f80000fff

def z909 : W := mkw 0x844403f000087b00 0x9088807e00010f60 0x0000033000006380 0x0000006600000c70

def z910 : W := mkw 0x173002800ea87b00 0x82e6005001d50f60 0xdffc03c00ff87f87 0xdbff807801ff0ff0

def z911 : W := mkw 0xc44403f090087fe0 0x9888807e12010ffc 0xc00003f000007fe0 0x1800007e00000ffc

def z912 : W := mkw 0xbddfdbff60000002 0x37bbfb7fec000000 0xfffffffff0060067 0xfffffffffe00c00c

def z913 : W := mkw 0x7bbbfc0ffff784e3 0x2f777f81fffef09c 0x3ffffc0fffff8067 0xe7ffff81fffff00c

def z914 : W := mkw 0x19bbdc0004f28001 0x23377b80009e5000 0x1fff1c0000f80002 0x83ffe380001f0000

def z915 : W := mkw 0x133004000ee28000 0x0266008001dc5000 0x1ffc00000fff8007 0xc3ff800001fff000

def z916 : W := mkw 0x422024009fffffe1 0x8844048013fffffc 0x400000000fffffe0 0x4800000001fffffc

def z917 : W := mkw 0xb9dfd97f60000002 0x373bfb2fec000000 0x3ffffc3ff0000007 0xa7ffff87fe000000

def z918 : W := mkw 0x1bbbfc000ff78001 0x23777f8001fef000 0x1ffffc000cff8002 0xa3ffff80019ff000

def z919 : W := mkw 0x199bdc0000520000 0x23337b80000a4000 0x1ffffc0000f80007 0xa3ffff80001f0000

def z920 : W := mkw 0xa44403fa80087f50 0xd488807f50010fea 0xc00003f380007f80 0x1800007e70000ff0

def z921 : W := mkw 0x00e1152454c2a2a8 0x001c22a48a985455 0xe1e31f3c7c07e3fa 0x3c3c63e78f80fc7f

def z922 : W := mkw 0x0a02a0008b050440 0x014054001160a088 0xfe03e3cf8f07fc7f 0x7fc07c79f1e0ff8f

def z923 : W := mkw 0xbddfdbff60000002 0x37bbfb7fec000000 0xbffcfcf3f0000005 0xb7ff9f9e7e000000

def z924 : W := mkw 0xbddfdbff60000002 0x37bbfb7fec000000 0xbffffffff007807f 0xb7fffffffe00f00f

def z925 : W := mkw 0xbdd793fe40000000 0x17baf27fc8000000 0xbffffffff0000007 0xb7fffffffe000000

def z926 : W := mkw 0xbddfdbff60000002 0x37bbfb7fec000000 0x1ffffcf3f0000007 0xa3ffff9e7e000000

def z927 : W := mkw 0x1bbbfc000ff78001 0x23777f8001fef000 0x1ffffc000ff98003 0x83ffff8001ff3000

def z928 : W := mkw 0x1bbbfc000ff78001 0x23777f8001fef000 0x1ffcfc000ff80007 0xc3ff9f8001ff0000

def z929 : W := mkw 0x1bbbfc008ff78441 0x23777f8011fef088 0x1ffffcc38fff9c07 0xe3ffff9871fff380

def z930 : W := mkw 0x13b958000ea00000 0x22772b0001d40000 0x1ffc1c000ff80007 0xc3ff838001ff0000

def z931 : W := mkw 0x977403f00ea87b00 0x92ee807e01d50f60 0x1ffc03f00ff87f83 0x83ff807e01ff0ff0

def z932 : W := mkw 0x2e02a28a8b055450 0x45c054515160aa8a 0xfe03ffffff07fc7f 0xffc07fffffe0ff8f

def z933 : W := mkw 0x688bfc0bb15784f1 0x6d117f81762af09e 0x2003fc0ff0078078 0x24007f81fe00f00f

def z934 : W := mkw 0xe44403fbb0087ff0 0xdc88807f76010ffe 0xe00003fff0007ff8 0x1c00007ffe000fff

def z935 : W := mkw 0xbddfdbff60010012 0x77bbfb7fec002002 0xbffffffff001801f 0xb7fffffffe003003

def z936 : W := mkw 0x1bbbfc045ff780a9 0x23777f808bfef015 0xffffff0c7fffe07f 0xffffffe18ffffc0f

def z937 : W := mkw 0x1bb390000ea18001 0x2376720001d43000 0x1fff00000f398003 0x03ffe00001e73000

def z938 : W := mkw 0x199bd80120000000 0x23337b0024000000 0x3ffffc03f0000007 0xa7ffff807e000000

def z939 : W := mkw 0x844403f000087b00 0x9088807e00010f60 0xc00003f00c007f86 0x5800007e01800ff0

def z940 : W := mkw 0x422024009fffddf1 0x4844048013fffbbe 0x400000000ffffff8 0x4800000001ffffff

def z941 : W := mkw 0x1b3aec000ff78001 0x23675d8001fef000 0x1ffce0000fff8007 0xc3ff9c0001fff000

def z942 : W := mkw 0x1bbbfc001ff7a2a9 0x23777f8003fef455 0x1ffffc000fff8387 0xe3ffff8001fff070

def z943 : W := mkw 0x1bbbfc000ff7d011 0x63777f8001fefa02 0x1ffffc000fffe01f 0xe3ffff8001fffc03

def z944 : W := mkw 0x13384c000ef20000 0x0267098001de4000 0x1ffc1c000ff80007 0xc3ff838001ff0000

def z945 : W := mkw 0x1bbbd8000eb18001 0x23777b0001d63000 0x1fff00000c398002 0x03ffe00001873000

def z946 : W := mkw 0x00c11124500022a8 0x001822248a000455 0xe1e31f3c7c07e3fe 0xfc3c63e78f80fc7f

def z947 : W := mkw 0xbd9fdadf60000002 0x37b3fb5bec000000 0x3ffffccff0000007 0xa7ffff99fe000000

def z948 : W := mkw 0xbddfdbff60082b02 0xb7bbfb7fec010560 0xbffffffff0000387 0xb7fffffffe000070

def z949 : W := mkw 0x3bbbfc0edff784f9 0x67777f81dbfef09f 0x3ffffc0fffff807f 0xe7ffff81fffff00f

def z950 : W := mkw 0x111c485120000000 0x0223890a24000000 0xbffcfcf3f0000007 0xb7ff9f9e7e000000

def z951 : W := mkw 0x399fd85f60000002 0x2733fb0bec000000 0xbffffcfff0000007 0xb7ffff9ffe000000

def z952 : W := mkw 0xbddfdbff60000002 0x37bbfb7fec000000 0xbffffffffc078007 0xf7ffffffff80f000

def z953 : W := mkw 0x133004000ef28001 0x0266008001de5000 0x1ffc00000ff80007 0xc3ff800001ff0000

def z954 : W := mkw 0x3bbbfc0e4ff78003 0x27777f81c9fef000 0x1ffffc0c0fff8007 0xe3ffff8181fff000

def z955 : W := mkw 0x95dd5bf560000000 0x12bbab7eac000000 0xbffffffff0000007 0xb7fffffffe000000

def z956 : W := mkw 0x688bfc0ff15784e3 0x2d117f81fe2af09c 0x2003fc0ff0078060 0x24007f81fe00f00c

def z957 : W := mkw 0x00e1112444802200 0x001c222488900440 0xe1e31f3c7cc7e3fe 0xfc3c63e78f98fc7f

def z958 : W := mkw 0x000c4c51304a09a0 0x0001898a26094134 0xe01cfcf3f3fe1fe5 0xfc039f9e7e7fc3fc

def z959 : W := mkw 0x5bbbfc01bff784e1 0x2b777f8037fef09c 0xfffffc33ffff83e7 0xffffff867ffff07c

def z960 : W := mkw 0x133020008fa40440 0x0266040011f48088 0xfffce0c38ffe1c67 0xffff9c1871ffc38c

def z961 : W := mkw 0x133848000eb00001 0x2267090001d60000 0x1ffc00000ff80007 0xc3ff800001ff0000

def z962 : W := mkw 0x19bbfc0005f78001 0x23377f8000bef000 0x1ffffc0000ff8007 0xa3ffff80001ff000

def z963 : W := mkw 0xbddfdbff60000002 0x37bbfb7fec000000 0x3ffffcfff0000001 0xa7ffff9ffe000000

def z964 : W := mkw 0x844403f000087b00 0x9088807e00010f60 0xe00303fc0c07fffe 0x7c00607f8180ffff

def z965 : W := mkw 0x977403f00ea87b00 0x92ee807e01d50f60 0x1ffc00f00ff81f87 0xc3ff801e01ff03f0

def z966 : W := mkw 0x133000000ea00000 0x0266000001d40000 0x1ffc00000f380003 0x03ff800001e70000

def z967 : W := mkw 0xbddfdbff60000002 0x37bbfb7fec000000 0xfffffffff000607f 0xbffffffffe000c0f

def z968 : W := mkw 0x022c48512ea87b00 0x8045890a25d50f60 0xe01cfcf3fff87f85 0xfc039f9e7fff0ff0

def z969 : W := mkw 0x133000000ea07200 0x8266000001d40e40 0x1ffc00000ff86007 0xc3ff800001ff0c00

def z970 : W := mkw 0xbddfdbff60000002 0x37bbfb7fec000000 0x3fffffcff0000003 0x27fffff9fe000000

def z971 : W := mkw 0x99dfd97560000002 0x333bfb2eac000000 0xbffffcf3f0000007 0xb7ffff9e7e000000

def z972 : W := mkw 0x1bbbfc008ff78441 0x23777f8011fef088 0x3ffffc038fff8067 0xe7ffff8071fff00c

def z973 : W := mkw 0x0060052014c222a0 0x000c00a402984454 0xe1e31f3c7cc7e3fe 0xfc3c63e78f98fc7f

def z974 : W := mkw 0x977403f00ea87b00 0x92ee807e01d50f60 0xfffc03fc0ff87fff 0xdfff807f81ff0fff

def z975 : W := mkw 0x1bbbfc044ff78009 0x23777f8089fef001 0x1ffffc0c0fff801f 0xe3ffff8181fff003

def z976 : W := mkw 0x2ccfdbff60000000 0x0599fb7fec000000 0xbffffffff0000007 0xb7fffffffe000000

def z977 : W := mkw 0x3bbbfc0a8ff78451 0x67777f8151fef08a 0xffffff0f8fffe07f 0xffffffe1f1fffc0f

def z978 : W := mkw 0xbddfdbff60005002 0x37bbfb7fec000a00 0xfffffffff0007c07 0xbffffffffe000f80

def z979 : W := mkw 0x1bbbfc000ff78001 0x23777f8001fef000 0x1ffcfc000fff8001 0xc3ff9f8001fff000

def z980 : W := mkw 0x3d9bda8f60000002 0x27b37b51ec000000 0xbfffffcff0000007 0xb7fffff9fe000000

def z981 : W := mkw 0x11186c0001560000 0x02230d80002ac000 0x1ffcfc0003fe0007 0xe3ff9f80007fc000

def z982 : W := mkw 0x1b9bfc000b778001 0x23737f80016ef000 0x1ffffc00033f8007 0xa3ffff800067f000

def z983 : W := mkw 0xeccffffff15e0de2 0x3d99fffffe2bc1bc 0xe003fffff0061fe0 0x3c007ffffe00c3fc

def z984 : W := mkw 0x1bbbfc000ff78001 0x23777f8001fef000 0xbffffcc38fff8007 0xf7ffff9871fff000

def z985 : W := mkw 0xa44403ffe0087f52 0xd488807ffc010fea 0xe00003fff0007ff8 0x1c00007ffe000fff

def z986 : W := mkw 0x19bbdc0004f28001 0x23377b80009e5000 0x1ffffc000cff8007 0xe3ffff80019ff000

def z987 : W := mkw 0x1bbbfc001ff780a1 0x23777f8003fef014 0x3ffffc007fff8067 0xe7ffff800ffff00c

def z988 : W := mkw 0x19bbdc0004f28001 0x23377b80009e5000 0x1ffcfc0000f80001 0x83ff9f80001f0000

def z989 : W := mkw 0x1bbbfc000ff7d001 0x23777f8001fefa00 0x5ffffc000ffffc07 0xebffff8001ffff80

def z990 : W := mkw 0x1b3ae8000fb50001 0x23675d0001f6a000 0x1ffce0000f380003 0x03ff9c0001e70000

def z991 : W := mkw 0x288bfc0ed15784f9 0x65117f81da2af09f 0x2003fc0ff0078078 0x24007f81fe00f00f

def z992 : W := mkw 0x1bb390000ea00000 0x2376720001d40000 0x1fff00000ff80007 0xc3ffe00001ff0000

def z993 : W := mkw 0xbddfdbff60000002 0x37bbfb7fec000000 0xfffffffffc006007 0xffffffffff800c00

def z994 : W := mkw 0x1bbbf8000fb58001 0x23777f0001f6b000 0x1ffffc000f398007 0xa3ffff8001e73000

def z995 : W := mkw 0x133020000fa50000 0x0266040001f4a000 0x1ffc00000fff8007 0xc3ff800001fff000

def z996 : W := mkw 0x3bbbfc0f7ff780ab 0x27777f81effef015 0x3ffffc0fffff807f 0xe7ffff81fffff00f

def z997 : W := mkw 0x400c6c51b15e0de0 0x08018d8a362bc1bc 0xe01ffcf3ffff9fe7 0xfc03ff9e7ffff3fc

def z998 : W := mkw 0x1bbbfc000ff78001 0x23777f8001fef000 0x1ffcfc0003fe0005 0xe3ff9f80007fc000

def z999 : W := mkw 0x844403f010087ba8 0x9088807e02010f75 0xc00003f000007ff8 0x1800007e00000fff

def z1000 : W := mkw 0x937401700ea82b00 0x926e802e01d50560 0xdffc00f00ff81f87 0xdbff801e01ff03f0

def z1001 : W := mkw 0x5bbbfc009ff784e1 0x2b777f8013fef09c 0x1ffffc000fff8067 0xe3ffff8001fff00c

def z1002 : W := mkw 0x844403f120087b00 0x9088807e24010f60 0xe00003f3f0007f80 0x1c00007e7e000ff0

def z1003 : W := mkw 0x060022808b045440 0x00c0045011608a88 0xfe03e3cf8f07fc7f 0x7fc07c79f1e0ff8f

def z1004 : W := mkw 0x844403f440087b08 0x9088807e88010f61 0xc00003fc00007f98 0x1800007f80000ff3

def z1005 : W := mkw 0x977403f00ea87b00 0x92ee807e01d50f60 0xdfff03fc0ff9ff9f 0xdbffe07f81ff3ff3

def z1006 : W := mkw 0xe44403ffe0080d42 0x1c88807ffc0101a8 0xa00003fff0001c00 0x1400007ffe000380

def z1007 : W := mkw 0x1bbbfc000ff7a209 0x23777f8001fef441 0x1ffffc000fffe01f 0xe3ffff8001fffc03

def z1008 : W := mkw 0x975403f00a085900 0x12ea807e01410b20 0xdffc03f00ff87f87 0xdbff807e01ff0ff0

def z1009 : W := mkw 0xbddbdbaf60000002 0x37bb7b75ec000000 0xbfe3ffcff0000007 0x37fc7ff9fe000000

def z1010 : W := mkw 0xbff393ae4ea0f20a 0xb7fe7275c9d41e41 0x1fe3030c0c01e01a 0x03fc606181803c03

def z1011 : W := mkw 0xa44403fb20087b02 0x9488807f64010f60 0xc00003f380007f80 0x1800007e70000ff0

def z1012 : W := mkw 0x977403f56ea87b02 0x92ee807eadd50f60 0xdffc03f07ff87f87 0xdbff807e0fff0ff0

def z1013 : W := mkw 0x1bb390000ea18001 0x2376720001d43000 0x1fff00000cf98002 0x83ffe000019f3000

def z1014 : W := mkw 0x400c6c51b15e0de0 0x08018d8a362bc1bc 0xe01cfcf3f3f81fe1 0x9c039f9e7e7f03fc

def z1015 : W := mkw 0x1bbbfc000ff78001 0x23777f8001fef000 0xbffffc307fff8007 0xf7ffff860ffff000

def z1016 : W := mkw 0x133020000fb50001 0x0266040001f6a000 0x1ffc00000ff80007 0xc3ff800001ff0000

def z1017 : W := mkw 0x066403f00e887b00 0x00cc807e01d10f60 0xdffc03f00ff87f87 0xdbff807e01ff0ff0

def z1018 : W := mkw 0x799bfc0ff15604e2 0x2f337f81fe2ac09c 0x3ffffc0ff3fe0067 0xe7ffff81fe7fc00c

def z1019 : W := mkw 0x19bbfc0005f68001 0x23377f8000bed000 0x1ffffc0003fe0007 0xe3ffff80007fc000

def z1020 : W := mkw 0x137401700ea82b00 0x026e802e01d50560 0xdffc03f00ff87f87 0xdbff807e01ff0ff0

def z1021 : W := mkw 0x13b97c000ff68000 0x02772f8001fed000 0x1ffffc000fff8007 0xe3ffff8001fff000

def z1022 : W := mkw 0x3bbbfc0a8ff78451 0x67777f8151fef08a 0xfffffccf8fff9c7f 0xffffff99f1fff38f

def z1023 : W := mkw 0x177003a00ea07200 0x02ee007401d40e40 0xdffc03f00ff87f87 0xdbff807e01ff0ff0

def z1024 : W := mkw 0x846403f004887b00 0x908c807e00910f60 0xc00003f00cc07f80 0x5800007e01980ff0

def z1025 : W := mkw 0x399bd80f60000002 0x27337b01ec000000 0x3fe3fc0ff0000002 0x27fc7f81fe000000

def z1026 : W := mkw 0x1b3aec000ff70000 0x03675d8001fee000 0x1ffffc000fff8007 0xe3ffff8001fff000

def z1027 : W := mkw 0x2c22868a14c2a2a8 0x058450d142985455 0xfe03e3cf8cc7e3ff 0x7fc07c79f198fc7f

def z1028 : W := mkw 0x957403f004a82b00 0x92ae807e00950560 0xdffc03f003f81f87 0xdbff807e007f03f0

def z1029 : W := mkw 0x133000000ea00000 0x0266000001d40000 0xdffc03000ff86007 0xdbff806001ff0c00

def z1030 : W := mkw 0xc44403f1b0080de0 0x1888807e360101bc 0xe00003f3f0001fe0 0x1c00007e7e0003fc

def z1031 : W := mkw 0x3ddbdbae40000000 0x27bb7b75c8000000 0xbffffffff0000007 0xb7fffffffe000000

def z1032 : W := mkw 0x133004001ee200a0 0x0266008003dc4014 0xfffc1c307ffe03e7 0xffff83860fffc07c

def z1033 : W := mkw 0x13b110000ea08001 0x2276220001d41000 0x1ffc00000ff80007 0xc3ff800001ff0000

def z1034 : W := mkw 0xa44403fed0087ff8 0xd488807fda010fff 0xe00003fff0007ff8 0x1c00007ffe000fff

def z1035 : W := mkw 0x022024009feffff8 0xc044048013fdffff 0x400000000ffffff8 0x4800000001ffffff

def z1036 : W := mkw 0x1b3280000ea10001 0x2366500001d42000 0x1ffc00000ff80007 0xc3ff800001ff0000

def z1037 : W := mkw 0x2e02a28a8b055450 0x45c054515160aa8a 0x5e03e3cf8f07fc7b 0x4bc07c79f1e0ff8f

def z1038 : W := mkw 0x91fd5d7574eaabaa 0xb23fabaeae9d5575 0x01fc1c3070f80380 0x803f83860e1f0070

def z1039 : W := mkw 0x00a1140014c280a0 0x0014228002985014 0xe1e31f3c7cc7e3fe 0xfc3c63e78f98fc7f

def z1040 : W := mkw 0x00086c00915604e0 0x00010d80122ac09c 0xe01cfcf3f3fe1fe5 0xfc039f9e7e7fc3fc

def z1041 : W := mkw 0x1bbbdc000ee28000 0x23777b8001dc5000 0x1ffffc000fff8007 0xe3ffff8001fff000

def z1042 : W := mkw 0x977403f44ea87b00 0x92ee807e89d50f60 0xfffc03fc7ff87f87 0xdfff807f8fff0ff0

def z1043 : W := mkw 0xa44403fa00087b00 0x9488807f40010f60 0xe00003ff80007f80 0x1c00007ff0000ff0

def z1044 : W := mkw 0x844403f440087b00 0x9088807e88010f60 0xe00003fc70007f80 0x1c00007f8e000ff0

def z1045 : W := mkw 0x199bfc0001578001 0x23337f80002af000 0x1ffffc0003ff8007 0xe3ffff80007ff000

def z1046 : W := mkw 0x400c6c51b15e0de0 0x08018d8a362bc1bc 0x201cfcf3f3fe1fe1 0xa4039f9e7e7fc3fc

def z1047 : W := mkw 0x1bbbf8000fb58001 0x23777f0001f6b000 0x1fffe0000f3f8007 0x63fffc0001e7f000

def z1048 : W := mkw 0x1bbbfc000ff78001 0x23777f8001fef000 0x1ffffc0003f80007 0xa3ffff80007f0000

def z1049 : W := mkw 0x844403f000087b00 0x9088807e00010f60 0x000003c000007c00 0x0000007800000f80

def z1050 : W := mkw 0x9ddfdbf120000000 0x33bbfb7e24000000 0xbffffff3f0000007 0xb7fffffe7e000000

def z1051 : W := mkw 0xbddfdbff60080902 0x37bbfb7fec010120 0xbffffffff3381c07 0xb7fffffffe670380

def z1052 : W := mkw 0x1bbbfc008ff78441 0x23777f8011fef088 0xffffffcf8ffffc7f 0xfffffff9f1ffff8f

def z1053 : W := mkw 0x955403f000087b00 0x92aa807e00010f60 0xdffc03f003f87f87 0xdbff807e007f0ff0

def z1054 : W := mkw 0x13b97c000ff78001 0x22772f8001fef000 0x1ffc1c000fff8007 0xc3ff838001fff000

def z1055 : W := mkw 0x1bbbfc001ff780a9 0x23777f8003fef015 0x1ffffc000fff807f 0xe3ffff8001fff00f

def z1056 : W := mkw 0x133000000ea00000 0x0266000001d40000 0x1ffc00000cf80002 0x83ff8000019f0000

def z1057 : W := mkw 0xbddfdbff6000800a 0x37bbfb7fec001001 0xbffffffff001801f 0xb7fffffffe003003

def z1058 : W := mkw 0x3bbbfc0a0ff78001 0x27777f8141fef000 0x3ffffc0f8fff8007 0xe7ffff81f1fff000

def z1059 : W := mkw 0x957403f004882b00 0x12ae807e00910560 0xdffc03f00ff87f87 0xdbff807e01ff0ff0

def z1060 : W := mkw 0x133000000ea00000 0x0266000001d40000 0x1fff00000fff8007 0xe3ffe00001fff000

def z1061 : W := mkw 0x844403f000087b00 0x9088807e00010f60 0xc00003f000c07f84 0xd800007e00180ff0

def z1062 : W := mkw 0x133400500ea87b00 0x8266800a01d50f60 0xdffc00f00ff87f87 0xdbff801e01ff0ff0

def z1063 : W := mkw 0x400c6c51b15e0de0 0x08018d8a362bc1bc 0xe01cfffff3fe7ffd 0xfc039ffffe7fcfff

def z1064 : W := mkw 0xac46a3fa810d7f50 0xd588d47f5021afea 0xe003e3ff8007fff8 0x3c007c7ff000ffff

def z1065 : W := mkw 0x1bbbfc001ff7a2a9 0x23777f8003fef455 0xffffff0c0fffe3ff 0xffffffe181fffc7f

def z1066 : W := mkw 0x1bbbdc000ef28001 0x23777b8001de5000 0x1ffffc000ff80007 0xe3ffff8001ff0000

def z1067 : W := mkw 0x137001200ea87b00 0x826e002401d50f60 0xdffc03300ff87f87 0xdbff806601ff0ff0

def z1068 : W := mkw 0x1bbbfc000ff7a201 0x23777f8001fef440 0x5ffffc000fffe387 0xebffff8001fffc70

def z1069 : W := mkw 0x95dd5bf560000002 0x32bbab7eac000000 0xbffcfff3f0000007 0xb7ff9ffe7e000000

def z1070 : W := mkw 0x13386c000ff78001 0x02670d8001fef000 0x1ffcfc000fff8007 0xe3ff9f8001fff000

def z1071 : W := mkw 0x400c6c51b15e0de0 0x08018d8a362bc1bc 0xe01cfcf3fffffffd 0xfc039f9e7fffffff

def z1072 : W := mkw 0x3bbbfc0a0ff78011 0x67777f8141fef002 0x1ffffc0c0fff801f 0xe3ffff8181fff003

def z1073 : W := mkw 0x977403f44ea87b08 0x92ee807e89d50f61 0xdffc03fc0ff87f9f 0xdbff807f81ff0ff3

def z1074 : W := mkw 0x1b9bf8000b350001 0x23737f000166a000 0x1ffffc000f3f8007 0xe3ffff8001e7f000

def z1075 : W := mkw 0xbddfdbff60002202 0x37bbfb7fec000440 0xfffffffff0006387 0xbffffffffe000c70

def z1076 : W := mkw 0x977403f00ea87b00 0x92ee807e01d50f60 0xffff03fc0ff87f87 0xffffe07f81ff0ff0

def z1077 : W := mkw 0x1bbbfc009ff7f6f9 0x63777f8013fefedf 0x5ffffc000fffffff 0xebffff8001ffffff

def z1078 : W := mkw 0x1bbbfc000ff78001 0x23777f8001fef000 0x1fffe0000fff8003 0x43fffc0001fff000

def z1079 : W := mkw 0x1bbbfc001ff780a1 0x23777f8003fef014 0xffffff3c7fffe3ff 0xffffffe78ffffc7f

def z1080 : W := mkw 0x975403f00a285900 0x92ea807e01450b20 0xdffc03f003f81f87 0xdbff807e007f03f0

def z1081 : W := mkw 0x19bbfc0005d68000 0x23377f8000bad000 0x1ffffc000fff8007 0xe3ffff8001fff000

def z1082 : W := mkw 0x844403f000087b00 0x9088807e00010f60 0xc00003f003007f85 0x5800007e00600ff0

def z1083 : W := mkw 0xb77403fb2ea87b02 0x96ee807f65d50f60 0xdffc03f38ff87f87 0xdbff807e71ff0ff0

def z1084 : W := mkw 0x1bbbfc045ff780a9 0x23777f808bfef015 0x1ffffc007fff8007 0xe3ffff800ffff000

def z1085 : W := mkw 0x400c6c51b15e0de0 0x08018d8a362bc1bc 0xe01ffffff3fe1fe7 0xfc03fffffe7fc3fc

def z1086 : W := mkw 0x977403f00ea80900 0x12ee807e01d50120 0xdffc03f00ff81f87 0xdbff807e01ff03f0

def z1087 : W := mkw 0x000c6851a10c0d40 0x00018d0a342181a8 0xe01cfcf3f3fe1fe5 0xfc039f9e7e7fc3fc

def z1088 : W := mkw 0x5bbbfc01bff784e1 0x2b777f8037fef09c 0xfffffcc3ffff9c67 0xffffff987ffff38c

def z1089 : W := mkw 0xe44403fff0082fea 0x1c88807ffe0105fd 0xe00003fff0007ff8 0x1c00007ffe000fff

def z1090 : W := mkw 0x00042450914e0de0 0x0000848a1229c1bc 0xe01cfcf3f3fe1fe5 0xfc039f9e7e7fc3fc

def z1091 : W := mkw 0x00e1152454f2a2a9 0x001c22a48a9e5455 0xe1e31f3c7cffe3fe 0xfc3c63e78f9ffc7f

def z1092 : W := mkw 0x977403f00ea87b00 0x92ee807e01d50f60 0x9ffc03f003f81f87 0x93ff807e007f03f0

def z1093 : W := mkw 0x1bb3b4000fe78000 0x0376768001fcf000 0x1ffffc000fff8007 0xe3ffff8001fff000

def z1094 : W := mkw 0x1130000004a00000 0x0226000000940000 0x1ffc000000f80007 0x83ff8000001f0000

def z1095 : W := mkw 0x422024009fff7ff0 0xc844048013ffeffe 0x400000000ffffff8 0x4800000001ffffff

def z1096 : W := mkw 0x1bbbfc000ff78001 0x23777f8001fef000 0x1ffffc0003ff8001 0xa3ffff80007ff000

def z1097 : W := mkw 0x3bbbd80f6ea00002 0x27777b01edd40000 0x3ffffc0ffff80007 0xe7ffff81ffff0000

def z1098 : W := mkw 0x1bbbfc045ff7a2a9 0x23777f808bfef455 0x7ffffc0c7fffe3ff 0xefffff818ffffc7f

def z1099 : W := mkw 0x400c6c51b15e0de0 0x08018d8a362bc1bc 0xa01cfcf3f3f81f85 0xb4039f9e7e7f03f0

def z1100 : W := mkw 0xc44c6ff1b15e7fe0 0x98898dfe362bcffc 0xe000fff3f0067fe0 0x3c001ffe7e00cffc

def z1101 : W := mkw 0x1bbbfc008ff7d451 0x63777f8011fefa8a 0xffffff0c0ffffc7f 0xffffffe181ffff8f

def z1102 : W := mkw 0xbddfdbff6000220a 0x37bbfb7fec000441 0xbffffffff000601f 0xb7fffffffe000c03

def z1103 : W := mkw 0xbd5ecbfb20000002 0x37abd97f64000000 0xbffcfff3f0000007 0xb7ff9ffe7e000000

def z1104 : W := mkw 0xb77403fa0ea87b00 0x96ee807f41d50f60 0xfffc03ff8ff87f87 0xdfff807ff1ff0ff0

def z1105 : W := mkw 0x1bb3b4000ff78001 0x2376768001fef000 0x1fff00000fff8007 0xc3ffe00001fff000

def z1106 : W := mkw 0x13b95c000ef28001 0x22772b8001de5000 0x1ffc1c000cf80002 0x83ff8380019f0000

def z1107 : W := mkw 0x3bbbfc0a8ff7d451 0x67777f8151fefa8a 0x7ffffc0f8ffffc7f 0xefffff81f1ffff8f

def z1108 : W := mkw 0x973402d00ea85900 0x92e6805a01d50b20 0xdffc00f00ff81f87 0xdbff801e01ff03f0

def z1109 : W := mkw 0x1bbbf8000fa50000 0x23777f0001f4a000 0x1ffffc000fff8007 0xe3ffff8001fff000

def z1110 : W := mkw 0x1bbbfc001ff780a1 0x23777f8003fef014 0x5ffffc000fff83e7 0xebffff8001fff07c

def z1111 : W := mkw 0x131000000a200000 0x0262000001440000 0x1ffc000003380007 0x83ff800000670000

def z1112 : W := mkw 0x133004001ee2a2a8 0x0266008003dc5455 0x5ffc00000fffe3ff 0xcbff800001fffc7f

def z1113 : W := mkw 0x19dfd97560000000 0x233bfb2eac000000 0xbffffffff0000007 0xb7fffffffe000000

def z1114 : W := mkw 0x1bbbfc001ff7a2a9 0x23777f8003fef455 0xfffffc307fffe3ff 0xffffff860ffffc7f

def z1115 : W := mkw 0x00e1152454c2a2a8 0x001c22a48a985455 0xe1e31ffc7fc7ffff 0xfc3c63ff8ff8ffff

def z1116 : W := mkw 0x133000000ea05000 0x0266000001d40a00 0x5ffc00000ff87c07 0xcbff800001ff0f80

def z1117 : W := mkw 0x1bb3b0000fa58001 0x2376760001f4b000 0x1fffe0000fff8007 0xe3fffc0001fff000

def z1118 : W := mkw 0x1bbbfc008ff7d451 0x63777f8011fefa8a 0xfffffcc38ffffc7f 0xffffff9871ffff8f

def z1119 : W := mkw 0x13b110000ea00000 0x0276220001d40000 0x1fff1c000ff80007 0xe3ffe38001ff0000

def z1120 : W := mkw 0x00e1152454c2a2a8 0x001c22a48a985455 0x21e31f3c7cc7e3fa 0xa43c63e78f98fc7f

def z1121 : W := mkw 0x400c6c51b15e8de8 0x08018d8a362bd1bd 0xe01cfcf3f3ff9ffd 0xfc039f9e7e7ff3ff

def z1122 : W := mkw 0x844403f080087f40 0x9088807e10010fe8 0xe00003f380007fe0 0x1c00007e70000ffc

def z1123 : W := mkw 0x977403f00ea87b00 0x92ee807e01d50f60 0xdffc03f003f87f81 0x9bff807e007f0ff0

def z1124 : W := mkw 0xa44403ff70087baa 0x9488807fee010f75 0xe00003fff0007ff8 0x1c00007ffe000fff

def z1125 : W := mkw 0x688bfc0ff15704f2 0x6d117f81fe2ae09e 0x2003fc0ff0078078 0x24007f81fe00f00f

def z1126 : W := mkw 0x488bfc00915784e1 0x29117f80122af09c 0x0003fc0000078060 0x20007f800000f00c

def z1127 : W := mkw 0x1bbbfc056ff78003 0x23777f80adfef000 0x1ffffc007fff8007 0xe3ffff800ffff000

def z1128 : W := mkw 0x1b9bfc000b770001 0x23737f80016ee000 0x1ffffc0003fe0007 0xe3ffff80007fc000

def z1129 : W := mkw 0x3b32a00a8fa50450 0x4766540151f4a08a 0x3fffe00f8fff807f 0xe7fffc01f1fff00f

def z1130 : W := mkw 0xc44403f130087ba0 0x9888807e26010f74 0xc00003f070007f80 0x1800007e0e000ff0

def z1131 : W := mkw 0x1b32a4000ff78001 0x0366548001fef000 0x1fffe0000fff8007 0xe3fffc0001fff000

def z1132 : W := mkw 0x400c4851b0080de0 0x0801890a360101bc 0xe01cfcf3f3f81fe5 0xfc039f9e7e7f03fc

def z1133 : W := mkw 0x1b1ae8000b350001 0x23635d000166a000 0x1ffce00003380007 0x83ff9c0000670000

def z1134 : W := mkw 0x1bbbfc009ff784e1 0x23777f8013fef09c 0xfffffcf3ffff9fe7 0xffffff9e7ffff3fc

def z1135 : W := mkw 0xc44403f1a0087f40 0x9888807e34010fe8 0xc00003f380007f80 0x1800007e70000ff0

def z1136 : W := mkw 0x1bbbfc000ff78001 0x23777f8001fef000 0xdffffcc00fff9c07 0xfbffff9801fff380

def z1137 : W := mkw 0x844403f010087ba0 0x9088807e02010f74 0xe00003f070007fe0 0x1c00007e0e000ffc

def z1138 : W := mkw 0x1bbbf8000fb50001 0x23777f0001f6a000 0x1ffffc000ff80007 0xe3ffff8001ff0000

def z1139 : W := mkw 0xbddfdbff60280902 0xb7bbfb7fec050120 0xbffffffff0380007 0xb7fffffffe070000

def z1140 : W := mkw 0x00e1152454c2a2a8 0x001c22a48a985455 0x41e31f3c7cc7e3fa 0xc83c63e78f98fc7f

def z1141 : W := mkw 0x7bbbfc0bbff784f1 0x6f777f8177fef09e 0x3ffffc0fffff807f 0xe7ffff81fffff00f

def z1142 : W := mkw 0x1bbbf8000fb58001 0x23777f0001f6b000 0x1ffce00003380001 0x03ff9c0000670000

def z1143 : W := mkw 0xa44403fa00087b10 0xd488807f40010f62 0xc00003fc00007f98 0x1800007f80000ff3

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(1,[z0,z1,z2,z3,z4,z5]),(0,[z6,z7,z8,z2,z3,z4,z5])],[(0,[z6,z8,z2,z9,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z10,z5]),(0,[z11,z6,z2,z3,z12,z4,z5]),(0,[z6,z8,z2,z3,z4,z13,z5]),(0,[z6,z14,z8,z2,z3,z15,z5]),(0,[z6,z8,z2,z16,z17,z4,z5]),(0,[z6,z8,z18,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z19,z4,z5])],[(0,[z20,z6,z8,z2,z3,z4,z5]),(1,[z6,z2,z3,z12,z4,z21]),(0,[z6,z8,z2,z3,z4,z15,z5])],[(0,[z22,z6,z23,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z24,z4,z5]),(0,[z25,z6,z8,z2,z4,z5,z26])],[(0,[z11,z6,z8,z2,z27,z4,z5]),(0,[z6,z8,z2,z28,z3,z4,z5])],[(0,[z29,z6,z8,z2,z3,z4,z5]),(0,[z30,z6,z8,z31,z3,z4,z5]),(0,[z32,z6,z33,z2,z3,z4,z5]),(0,[z32,z8,z2,z3,z34,z4,z5]),(0,[z35,z6,z8,z2,z3,z4,z36]),(0,[z6,z8,z37,z2,z16,z3,z5]),(0,[z6,z8,z2,z38,z3,z4,z39]),(1,[z6,z8,z2,z4,z5,z40])],[(0,[z41,z6,z8,z2,z3,z4,z5]),(0,[z6,z42,z2,z3,z12,z4,z5])],[(0,[z6,z8,z2,z43,z3,z4,z5]),(0,[z6,z44,z8,z2,z3,z4,z5])]],
   [[(0,[z45,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z36,z5]),(0,[z6,z8,z2,z3,z4,z5,z46]),(0,[z6,z8,z2,z3,z47,z4,z5]),(0,[z6,z48,z8,z2,z3,z4,z5]),(0,[z6,z49,z8,z50,z3,z4,z5]),(0,[z6,z8,z51,z2,z3,z4,z5])],[(0,[z6,z8,z2,z3,z52,z4,z5]),(0,[z6,z8,z2,z3,z53,z4,z5]),(0,[z6,z23,z54,z2,z3,z4,z5]),(0,[z55,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z56,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z57])],[(0,[z6,z8,z58,z2,z3,z4,z5])],[(1,[z59,z8,z2,z3,z60,z5]),(0,[z6,z61,z8,z2,z3,z4,z5]),(0,[z6,z62,z8,z2,z3,z4,z5])],[(0,[z0,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z63,z3,z4,z5]),(0,[z6,z64,z8,z2,z3,z4,z5]),(0,[z65,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z66,z4,z5]),(1,[z6,z8,z2,z38,z4,z39])],[(0,[z6,z8,z67,z2,z3,z4,z5]),(0,[z68,z6,z23,z8,z2,z3,z5]),(0,[z6,z69,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z39,z70]),(0,[z6,z71,z8,z2,z3,z4,z5])],[(0,[z6,z1,z2,z3,z4,z15,z5]),(0,[z6,z8,z2,z3,z4,z72,z5]),(0,[z6,z8,z2,z3,z73,z4,z5])],[(0,[z74,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z3,z4,z5]),(0,[z75,z59,z8,z2,z3,z4,z5]),(0,[z76,z6,z8,z2,z3,z4,z5]),(0,[z77,z6,z8,z2,z3,z4,z5])]],
   [[(0,[z78,z6,z2,z3,z12,z4,z5]),(0,[z35,z6,z2,z3,z12,z4,z5]),(0,[z6,z8,z2,z3,z4,z79,z5]),(0,[z6,z8,z2,z3,z80,z4,z5])],[(0,[z6,z8,z81,z2,z3,z4,z5]),(0,[z82,z6,z8,z2,z3,z4,z5]),(0,[z6,z83,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z84,z4,z5]),(0,[z6,z83,z8,z85,z3,z4,z5]),(0,[z6,z8,z86,z2,z3,z4,z5]),(0,[z6,z87,z8,z2,z3,z4,z88]),(0,[z6,z8,z2,z3,z89,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z90]),(0,[z25,z6,z8,z2,z17,z4,z5]),(1,[z91,z6,z8,z2,z4,z5]),(0,[z6,z92,z8,z2,z3,z4,z70])],[(0,[z93,z6,z8,z2,z3,z4,z5]),(1,[z6,z23,z2,z3,z12,z5]),(0,[z94,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z95,z2,z3,z4,z5])],[(0,[z6,z8,z96,z2,z3,z4,z5]),(0,[z6,z8,z2,z97,z3,z4,z5]),(1,[z6,z8,z2,z3,z53,z4]),(0,[z6,z2,z3,z98,z12,z4,z5])],[(0,[z6,z8,z2,z3,z4,z99,z5])],[(0,[z6,z8,z2,z3,z4,z100,z5]),(0,[z6,z101,z8,z2,z3,z4,z5]),(0,[z102,z6,z23,z2,z3,z4,z5]),(0,[z6,z2,z3,z103,z12,z4,z5]),(0,[z25,z6,z8,z2,z3,z4,z39]),(1,[z6,z2,z3,z4,z5,z104]),(0,[z6,z8,z2,z38,z3,z4,z26])],[(0,[z6,z8,z2,z3,z105,z4,z5]),(0,[z106,z6,z8,z2,z3,z4,z5]),(0,[z68,z6,z8,z2,z3,z107,z5]),(0,[z6,z108,z8,z2,z3,z4,z5])],[(0,[z6,z85,z2,z3,z12,z4,z5]),(0,[z6,z8,z2,z3,z12,z4,z5]),(0,[z6,z109,z8,z2,z3,z4,z5]),(0,[z6,z110,z37,z2,z3,z4,z5])]],
   [[(0,[z6,z111,z8,z2,z3,z4,z5]),(0,[z6,z112,z8,z2,z3,z5,z70]),(0,[z6,z2,z113,z3,z12,z4,z5]),(0,[z6,z8,z114,z2,z3,z4,z5]),(0,[z6,z2,z3,z4,z115,z5,z116]),(0,[z6,z117,z8,z2,z3,z4,z5])],[(0,[z118,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z119,z2,z3,z4,z5])],[(0,[z6,z2,z3,z12,z4,z5,z120]),(0,[z6,z8,z2,z3,z4,z121,z5])],[(0,[z6,z8,z122,z2,z3,z4,z5]),(0,[z6,z123,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z124,z5]),(0,[z6,z23,z2,z3,z125,z4,z5]),(0,[z6,z87,z8,z2,z3,z125,z4]),(0,[z6,z126,z8,z2,z3,z4,z5])],[(0,[z6,z8,z2,z3,z127,z4,z5]),(0,[z6,z8,z2,z3,z4,z128,z5]),(0,[z6,z2,z3,z12,z4,z5,z129]),(0,[z6,z8,z2,z3,z4,z5,z130]),(0,[z6,z8,z131,z2,z3,z4,z5])],[(0,[z132,z6,z133,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z134]),(0,[z11,z6,z2,z3,z135,z4,z5]),(0,[z136,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z137]),(0,[z6,z138,z8,z2,z3,z4,z5])],[(0,[z59,z6,z8,z2,z3,z4,z5]),(1,[z6,z8,z2,z3,z139,z5]),(0,[z6,z23,z2,z3,z140,z4,z5]),(0,[z6,z2,z38,z3,z12,z4,z5]),(1,[z6,z8,z42,z113,z4,z5]),(0,[z68,z6,z8,z2,z3,z17,z5]),(0,[z6,z8,z37,z2,z3,z4,z39])],[(0,[z6,z23,z2,z3,z4,z15,z5]),(0,[z6,z2,z3,z12,z4,z5,z26])]],
   [[(0,[z6,z141,z8,z2,z3,z4,z5]),(0,[z6,z142,z8,z2,z3,z4,z5]),(0,[z6,z23,z50,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z143]),(0,[z144,z6,z8,z2,z3,z4,z5])],[(0,[z6,z145,z8,z2,z3,z4,z5]),(1,[z6,z146,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z147,z4,z5]),(1,[z6,z54,z2,z27,z4,z5]),(0,[z6,z2,z3,z12,z4,z5,z148]),(0,[z6,z8,z2,z3,z4,z149,z5]),(0,[z6,z8,z50,z2,z3,z56,z5]),(1,[z6,z8,z2,z3,z150,z4])],[(0,[z6,z8,z151,z2,z3,z4,z5]),(0,[z6,z8,z2,z152,z3,z4,z5]),(0,[z6,z153,z8,z2,z3,z4,z5])],[(0,[z6,z8,z2,z3,z4,z154,z5]),(0,[z6,z1,z2,z3,z12,z4,z5]),(0,[z132,z6,z8,z2,z155,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z156]),(0,[z6,z157,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z158]),(0,[z68,z6,z8,z2,z3,z5,z159])],[(0,[z160,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z161,z5])],[(0,[z6,z8,z2,z162,z3,z4,z5]),(1,[z6,z163,z2,z3,z4,z5]),(0,[z25,z6,z8,z2,z3,z4,z26])],[(0,[z6,z8,z2,z3,z164,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z165]),(0,[z6,z8,z2,z166,z3,z4,z5]),(0,[z6,z8,z167,z2,z3,z4,z5]),(0,[z6,z168,z8,z2,z3,z135,z5]),(0,[z6,z169,z8,z2,z3,z4,z5]),(0,[z68,z6,z2,z3,z12,z4,z5])],[(0,[z6,z8,z2,z3,z4,z5,z170]),(0,[z6,z8,z2,z171,z3,z4,z5]),(0,[z6,z8,z2,z3,z172,z4,z5]),(0,[z6,z8,z2,z3,z4,z173,z5])]],
   [[(0,[z6,z8,z2,z3,z4,z5,z174]),(0,[z175,z6,z23,z2,z3,z4,z5]),(0,[z6,z176,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z177,z5]),(0,[z6,z8,z2,z178,z3,z4,z5])],[(0,[z6,z179,z8,z2,z3,z4,z5]),(0,[z6,z131,z2,z3,z12,z4,z5]),(1,[z6,z49,z8,z3,z5,z116]),(0,[z6,z8,z131,z3,z4,z5,z88]),(0,[z180,z6,z8,z2,z3,z4,z5])],[(0,[z6,z8,z2,z113,z181,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z182]),(0,[z11,z6,z8,z2,z3,z4,z5]),(1,[z68,z6,z23,z2,z3,z5]),(0,[z6,z2,z16,z3,z12,z4,z5]),(0,[z183,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z184]),(0,[z6,z8,z185,z2,z3,z4,z5])],[(0,[z186,z6,z8,z2,z3,z4,z5]),(0,[z75,z6,z2,z3,z12,z4,z5]),(0,[z6,z8,z2,z3,z4,z115,z5])],[(0,[z187,z6,z8,z2,z3,z4,z5]),(0,[z6,z188,z8,z2,z3,z4,z5]),(0,[z78,z8,z2,z3,z4,z5,z120]),(0,[z6,z8,z189,z2,z3,z4,z5]),(0,[z6,z190,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z191]),(0,[z6,z8,z2,z3,z192,z4,z5]),(0,[z6,z8,z2,z4,z39,z5,z26]),(1,[z6,z2,z193,z3,z4,z5])],[(1,[z6,z8,z194,z2,z3,z4]),(0,[z195,z6,z8,z2,z3,z4,z5]),(0,[z196,z6,z8,z2,z3,z4,z5]),(0,[z6,z2,z27,z3,z4,z15,z5]),(0,[z197,z6,z2,z3,z12,z4,z5]),(0,[z6,z2,z3,z12,z17,z4,z5]),(0,[z6,z198,z199,z2,z3,z4,z5])],[(0,[z6,z200,z8,z2,z3,z4,z5]),(0,[z6,z23,z2,z3,z34,z4,z5]),(0,[z6,z8,z2,z3,z201,z4,z5]),(0,[z6,z8,z37,z2,z3,z4,z26]),(0,[z6,z8,z2,z3,z202,z4,z5])],[(0,[z6,z168,z8,z2,z3,z4,z5]),(0,[z6,z198,z23,z2,z3,z4,z5]),(0,[z6,z163,z8,z2,z3,z4,z5])]],
   [[(0,[z6,z8,z2,z3,z203,z4,z5]),(0,[z6,z8,z2,z3,z204,z4,z5]),(0,[z6,z8,z2,z3,z60,z4,z5]),(0,[z6,z8,z205,z2,z3,z4,z5])],[(0,[z32,z6,z206,z2,z3,z4,z5]),(0,[z6,z2,z3,z207,z12,z4,z5]),(0,[z6,z208,z8,z2,z3,z4,z5]),(0,[z6,z92,z8,z2,z3,z107,z5])],[(1,[z78,z8,z2,z3,z4,z120]),(0,[z6,z8,z2,z3,z4,z209,z5]),(0,[z6,z117,z2,z16,z3,z4,z5])],[(0,[z6,z8,z2,z3,z135,z4,z5]),(0,[z6,z54,z2,z27,z3,z4,z5]),(0,[z6,z8,z2,z17,z4,z5,z159])],[(0,[z59,z6,z210,z2,z3,z4,z5]),(0,[z6,z2,z3,z12,z4,z4,z5]),(0,[z25,z6,z92,z8,z2,z3,z4])],[(0,[z6,z211,z8,z2,z31,z3,z4]),(0,[z212,z6,z213,z2,z3,z4,z5]),(0,[z6,z8,z2,z113,z3,z4,z5]),(0,[z6,z8,z2,z3,z214,z4,z5])],[(0,[z6,z8,z2,z3,z4,z5,z40])],[(0,[z6,z8,z2,z3,z4,z5,z215]),(0,[z6,z8,z2,z3,z4,z216,z5]),(0,[z6,z8,z2,z3,z4,z217,z5]),(0,[z6,z8,z2,z3,z218,z4,z5]),(1,[z6,z210,z2,z3,z4,z5]),(0,[z6,z8,z219,z2,z3,z4,z5]),(0,[z6,z83,z54,z2,z3,z4,z5]),(0,[z6,z8,z220,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z221])]],
   [[(0,[z6,z222,z8,z2,z3,z4,z5]),(0,[z6,z8,z194,z2,z31,z3,z4]),(0,[z6,z8,z223,z2,z3,z4,z5]),(0,[z6,z224,z23,z2,z3,z4,z5]),(1,[z6,z23,z2,z3,z4,z5]),(0,[z6,z8,z2,z225,z3,z4,z5])],[(0,[z132,z6,z8,z2,z3,z4,z226]),(1,[z75,z8,z2,z3,z227,z5]),(0,[z78,z6,z8,z2,z3,z4,z5]),(0,[z35,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z228]),(0,[z6,z229,z8,z2,z3,z4,z5]),(1,[z6,z198,z2,z3,z4,z15]),(0,[z6,z69,z2,z3,z4,z5,z116]),(1,[z6,z92,z8,z37,z2,z3])],[(0,[z6,z8,z2,z3,z4,z5,z21]),(1,[z25,z6,z8,z2,z4,z26]),(0,[z6,z8,z2,z3,z107,z4,z70])],[],[(0,[z230,z6,z8,z2,z3,z4,z5]),(0,[z6,z85,z2,z231,z3,z4,z5]),(0,[z6,z8,z2,z231,z3,z4,z5])],[(0,[z22,z6,z2,z3,z12,z4,z5]),(0,[z8,z2,z3,z4,z36,z5,z120]),(0,[z6,z2,z3,z12,z4,z5,z88]),(0,[z6,z8,z2,z3,z232,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z233])],[(0,[z6,z8,z2,z3,z4,z5,z234]),(0,[z6,z8,z2,z3,z4,z5,z235]),(0,[z236,z6,z8,z2,z3,z4,z5]),(0,[z6,z199,z8,z2,z3,z4,z129]),(0,[z6,z8,z2,z3,z4,z5,z237])],[(1,[z6,z33,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z238,z5]),(0,[z6,z239,z8,z2,z3,z4,z5])]],
   [[(0,[z6,z8,z2,z240,z3,z4,z5]),(0,[z6,z83,z85,z2,z3,z4,z5])],[(0,[z6,z8,z2,z241,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z242]),(0,[z25,z6,z2,z3,z12,z4,z5]),(0,[z6,z92,z2,z3,z12,z4,z5]),(0,[z6,z8,z2,z3,z150,z4,z5])],[(0,[z6,z8,z243,z2,z3,z4,z5]),(0,[z6,z8,z244,z2,z3,z4,z5]),(0,[z6,z2,z27,z3,z12,z4,z5]),(0,[z6,z245,z8,z2,z3,z4,z5])],[(0,[z6,z8,z246,z2,z3,z4,z5]),(0,[z6,z23,z2,z27,z3,z4,z5]),(0,[z6,z247,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z248])],[(0,[z6,z8,z2,z3,z249,z4,z5])],[(0,[z6,z146,z8,z2,z3,z4,z5]),(0,[z6,z2,z250,z3,z12,z4,z5])],[(0,[z251,z6,z8,z2,z3,z4,z5]),(0,[z6,z2,z31,z3,z12,z4,z5]),(0,[z30,z6,z23,z2,z3,z4,z5]),(0,[z252,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z253]),(0,[z6,z8,z254,z2,z3,z4,z5])],[(0,[z6,z8,z2,z3,z4,z255,z5]),(0,[z6,z8,z2,z181,z3,z4,z5]),(0,[z6,z8,z2,z256,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z257]),(0,[z6,z258,z8,z2,z3,z4,z5]),(0,[z259,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z260,z2,z3,z4,z5])]],
   [[(0,[z6,z1,z2,z231,z3,z4,z5]),(0,[z261,z6,z8,z2,z3,z4,z5]),(0,[z78,z6,z8,z2,z3,z4,z36]),(0,[z78,z6,z87,z8,z2,z3,z4]),(0,[z35,z6,z87,z8,z2,z3,z4]),(0,[z6,z8,z2,z262,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z263]),(0,[z6,z49,z23,z2,z3,z4,z5]),(0,[z68,z6,z8,z2,z16,z4,z5])],[(0,[z264,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z265,z2,z3,z4,z5])],[(0,[z6,z8,z2,z266,z3,z4,z5]),(0,[z6,z198,z8,z2,z3,z4,z129]),(0,[z6,z8,z2,z3,z267,z4,z5])],[(0,[z6,z8,z2,z268,z3,z4,z5]),(0,[z68,z6,z8,z2,z3,z4,z269]),(0,[z68,z6,z8,z2,z4,z5,z159]),(0,[z6,z8,z2,z17,z4,z39,z5])],[(0,[z6,z1,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z270,z5]),(0,[z68,z6,z112,z8,z2,z3,z5]),(0,[z6,z8,z2,z3,z4,z271,z5]),(0,[z68,z6,z8,z37,z2,z3,z5]),(1,[z6,z8,z2,z3,z107,z70])],[(0,[z6,z23,z2,z3,z60,z4,z5]),(0,[z6,z23,z272,z2,z3,z4,z5]),(0,[z6,z112,z8,z2,z16,z3,z5]),(0,[z6,z2,z3,z12,z107,z4,z5]),(0,[z6,z273,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z274,z3,z4,z5]),(0,[z6,z8,z275,z2,z3,z4,z5])],[(0,[z6,z276,z2,z3,z135,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z277]),(0,[z6,z8,z2,z3,z4,z278,z5]),(0,[z11,z6,z8,z2,z135,z4,z5]),(0,[z279,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z280,z3,z4,z5]),(0,[z6,z2,z3,z12,z4,z5,z70]),(0,[z6,z8,z2,z281,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z159])],[(0,[z6,z282,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z283,z5]),(0,[z6,z8,z2,z284,z3,z4,z5]),(0,[z6,z8,z2,z285,z3,z4,z5]),(0,[z6,z49,z8,z2,z3,z56,z5]),(0,[z286,z6,z8,z2,z3,z4,z5]),(0,[z68,z6,z8,z2,z3,z4,z5])]],
   [[(1,[z6,z8,z2,z3,z203,z5]),(0,[z32,z175,z8,z2,z3,z4,z5]),(0,[z6,z23,z2,z3,z135,z4,z5]),(0,[z6,z8,z2,z287,z3,z4,z5]),(0,[z6,z288,z2,z3,z4,z5,z70])],[(0,[z6,z8,z289,z2,z3,z4,z5]),(1,[z6,z112,z2,z3,z12,z5]),(0,[z6,z8,z2,z250,z3,z4,z5]),(0,[z6,z8,z2,z3,z290,z4,z5]),(0,[z6,z8,z2,z291,z3,z4,z5]),(0,[z6,z8,z2,z292,z3,z4,z5])],[(0,[z293,z6,z8,z2,z3,z4,z5]),(0,[z294,z6,z8,z2,z3,z4,z5]),(1,[z6,z23,z2,z3,z5,z70]),(0,[z212,z6,z2,z3,z12,z4,z5]),(0,[z6,z87,z2,z3,z12,z4,z5]),(0,[z6,z8,z295,z2,z3,z4,z5])],[(0,[z6,z8,z2,z3,z296,z4,z5]),(0,[z6,z8,z2,z3,z4,z297,z5]),(0,[z6,z8,z2,z3,z4,z5,z298]),(0,[z6,z299,z8,z231,z3,z4,z5]),(0,[z300,z6,z8,z2,z3,z4,z5]),(0,[z6,z301,z8,z2,z3,z4,z5]),(0,[z302,z6,z2,z3,z12,z4,z5]),(1,[z6,z2,z303,z3,z12,z4]),(0,[z6,z8,z2,z3,z4,z5,z304]),(0,[z6,z8,z2,z3,z4,z305,z5]),(0,[z6,z306,z50,z2,z3,z4,z5]),(0,[z6,z8,z50,z3,z56,z4,z5])],[(0,[z75,z6,z8,z2,z3,z4,z5]),(0,[z6,z198,z2,z3,z4,z15,z5]),(0,[z6,z2,z3,z4,z307,z5,z70])],[(0,[z6,z2,z3,z12,z4,z308,z5])],[(0,[z197,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z309,z4,z5]),(0,[z310,z6,z8,z2,z3,z4,z5])],[(0,[z6,z8,z2,z3,z4,z311,z5]),(0,[z6,z312,z8,z2,z3,z4,z5])]],
   [[(0,[z6,z8,z2,z3,z4,z313,z5]),(0,[z6,z112,z23,z2,z3,z4,z5]),(0,[z6,z8,z2,z314,z3,z4,z5]),(0,[z68,z6,z8,z2,z3,z4,z315])],[(0,[z6,z8,z2,z3,z207,z4,z5]),(0,[z6,z8,z2,z316,z3,z4,z5]),(1,[z6,z8,z50,z3,z56,z5])],[(0,[z35,z6,z8,z131,z2,z3,z4]),(0,[z6,z8,z317,z2,z3,z4,z5])],[(0,[z8,z318,z2,z31,z3,z4,z5]),(0,[z319,z6,z8,z2,z3,z4,z5]),(0,[z6,z320,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z321,z3,z4,z5]),(0,[z6,z322,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z323,z5]),(0,[z6,z8,z2,z324,z3,z4,z5])],[(0,[z325,z6,z8,z2,z3,z4,z5]),(0,[z326,z6,z8,z2,z3,z4,z5]),(0,[z327,z6,z2,z3,z12,z4,z5]),(0,[z6,z8,z2,z328,z3,z4,z5]),(0,[z6,z8,z2,z3,z202,z5,z26])],[(0,[z132,z6,z2,z3,z12,z4,z5]),(0,[z6,z8,z2,z3,z4,z329,z5]),(1,[z6,z83,z85,z3,z4,z5])],[(0,[z6,z8,z2,z3,z4,z330,z5]),(0,[z6,z8,z2,z3,z4,z5,z331]),(0,[z6,z2,z27,z3,z135,z4,z5]),(0,[z6,z8,z2,z3,z53,z135,z4]),(0,[z6,z8,z332,z2,z3,z4,z5])],[(0,[z6,z8,z2,z333,z3,z4,z5]),(0,[z29,z6,z23,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z150,z4,z159])]],
   [[(0,[z6,z276,z2,z3,z4,z15,z5]),(0,[z334,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z120]),(0,[z41,z6,z23,z2,z3,z4,z5])],[(0,[z6,z8,z335,z2,z3,z4,z5]),(0,[z6,z8,z2,z336,z3,z4,z5]),(0,[z6,z2,z3,z4,z15,z5,z129]),(0,[z337,z6,z8,z2,z3,z4,z5])],[(0,[z6,z8,z2,z3,z338,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z129]),(0,[z6,z2,z3,z4,z5,z221,z159]),(1,[z6,z117,z2,z3,z4,z5])],[(0,[z32,z6,z8,z2,z34,z4,z5]),(0,[z339,z6,z8,z2,z3,z4,z5]),(1,[z6,z340,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z341,z5]),(0,[z6,z8,z2,z3,z342,z4,z5]),(0,[z343,z6,z8,z2,z3,z4,z5]),(0,[z68,z6,z8,z2,z4,z39,z5])],[(0,[z6,z299,z2,z3,z12,z4,z5]),(1,[z11,z6,z2,z135,z4,z5]),(0,[z6,z23,z2,z3,z4,z5,z257]),(0,[z6,z8,z2,z344,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z345,z5]),(0,[z6,z8,z346,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z12,z4,z21]),(0,[z6,z8,z2,z16,z3,z107,z5])],[(0,[z6,z8,z318,z2,z3,z4,z5]),(0,[z6,z23,z8,z2,z3,z238,z5]),(1,[z6,z8,z2,z3,z13,z5])],[(0,[z0,z6,z23,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z347,z4,z5]),(0,[z6,z8,z2,z3,z4,z348,z5]),(0,[z6,z8,z2,z3,z4,z349,z5]),(0,[z6,z8,z2,z3,z350,z4,z5]),(0,[z6,z8,z2,z3,z4,z39,z5]),(0,[z6,z8,z2,z3,z4,z351,z5])],[(0,[z6,z8,z276,z2,z3,z4,z5]),(0,[z6,z352,z8,z2,z3,z4,z5]),(0,[z6,z54,z2,z3,z12,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z148]),(0,[z6,z353,z8,z2,z3,z4,z5]),(0,[z6,z92,z8,z37,z2,z3,z5])]],
   [[(0,[z6,z8,z354,z2,z3,z4,z5]),(0,[z6,z355,z8,z2,z3,z4,z5]),(0,[z6,z23,z2,z3,z4,z36,z5]),(0,[z6,z8,z2,z3,z4,z5,z356]),(0,[z6,z8,z2,z3,z357,z4,z5]),(0,[z6,z8,z358,z2,z3,z4,z5])],[(0,[z359,z6,z8,z2,z3,z4,z5]),(0,[z6,z83,z199,z2,z3,z4,z5]),(0,[z6,z23,z2,z3,z56,z4,z5]),(1,[z6,z92,z23,z2,z3,z5]),(0,[z6,z8,z2,z3,z103,z4,z5])],[(0,[z6,z360,z8,z2,z3,z4,z5]),(0,[z361,z6,z8,z2,z3,z4,z5]),(0,[z6,z54,z8,z2,z27,z4,z5]),(0,[z6,z8,z2,z3,z362,z4,z5]),(0,[z25,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z363,z4,z5]),(0,[z6,z92,z8,z2,z3,z4,z5])],[(0,[z364,z6,z8,z2,z3,z4,z5]),(1,[z6,z206,z2,z3,z4,z5]),(0,[z6,z83,z23,z2,z3,z4,z5]),(0,[z6,z23,z2,z3,z4,z5,z159]),(0,[z6,z92,z23,z8,z2,z3,z5]),(0,[z6,z8,z365,z2,z3,z4,z5])],[(0,[z366,z6,z8,z2,z3,z4,z5]),(0,[z6,z199,z2,z27,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z116]),(0,[z6,z8,z2,z3,z367,z4,z5]),(0,[z6,z8,z2,z368,z3,z4,z5]),(0,[z6,z8,z2,z16,z3,z17,z5])],[(0,[z6,z6,z8,z2,z3,z4,z5]),(0,[z6,z369,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z370]),(1,[z6,z8,z2,z3,z371,z5]),(0,[z91,z6,z8,z2,z4,z5,z70])],[(0,[z6,z8,z2,z3,z372,z4,z5]),(0,[z6,z8,z2,z3,z4,z373,z5]),(0,[z6,z374,z8,z2,z3,z4,z5]),(1,[z6,z8,z2,z3,z4,z21]),(0,[z212,z6,z8,z3,z103,z4,z5]),(0,[z6,z8,z2,z3,z375,z4,z5])],[(0,[z6,z8,z376,z2,z3,z4,z5]),(0,[z6,z377,z8,z2,z3,z4,z5]),(0,[z6,z8,z378,z2,z3,z4,z5]),(0,[z379,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z380,z5]),(0,[z6,z8,z2,z381,z3,z4,z5])]],
   [[(0,[z6,z199,z8,z2,z3,z4,z70]),(0,[z382,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z3,z56,z4,z5,z116])],[(0,[z6,z8,z2,z3,z56,z227,z5]),(0,[z6,z8,z2,z3,z125,z4,z120]),(0,[z6,z8,z2,z3,z4,z5,z383]),(0,[z6,z8,z2,z16,z3,z5,z159])],[],[(0,[z6,z8,z2,z3,z384,z4,z5]),(0,[z6,z8,z2,z3,z385,z4,z5]),(0,[z6,z8,z2,z3,z386,z4,z5]),(0,[z6,z2,z3,z135,z12,z4,z5]),(0,[z6,z387,z8,z2,z3,z4,z5]),(0,[z388,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z389,z3,z4,z5]),(0,[z6,z8,z2,z3,z17,z4,z5]),(0,[z6,z8,z2,z3,z371,z5,z26]),(0,[z6,z8,z37,z2,z3,z4,z5])],[(0,[z6,z8,z2,z3,z390,z4,z5]),(0,[z6,z8,z2,z391,z3,z4,z5]),(0,[z392,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z139,z135,z5]),(0,[z6,z8,z2,z3,z4,z5,z393]),(0,[z6,z8,z42,z113,z3,z4,z5]),(0,[z6,z8,z394,z2,z3,z4,z5]),(0,[z6,z395,z8,z2,z3,z4,z5])],[(0,[z6,z276,z2,z3,z12,z4,z5]),(1,[z6,z133,z2,z3,z4,z5]),(0,[z6,z8,z2,z396,z3,z4,z5]),(0,[z6,z2,z3,z12,z125,z4,z5])],[(0,[z6,z8,z2,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z226,z5]),(1,[z132,z8,z31,z3,z4,z5])],[(0,[z6,z23,z2,z3,z12,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z104])]],
   [[(0,[z59,z6,z23,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z397])],[(0,[z6,z8,z2,z3,z4,z398,z5]),(0,[z6,z8,z194,z2,z3,z4,z5]),(0,[z6,z399,z8,z2,z3,z4,z5]),(0,[z400,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z401,z4,z5]),(0,[z402,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z403]),(0,[z404,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z405,z2,z3,z4,z5]),(1,[z6,z2,z3,z4,z307,z5])],[(0,[z6,z8,z2,z3,z406,z4,z5]),(0,[z407,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z408,z4,z5]),(0,[z409,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z4,z5]),(0,[z6,z2,z231,z3,z4,z15,z5]),(0,[z6,z142,z23,z2,z3,z4,z5]),(0,[z6,z23,z8,z2,z3,z12,z5])],[(1,[z6,z8,z2,z155,z4,z5]),(0,[z6,z410,z8,z2,z3,z4,z5]),(0,[z32,z6,z2,z3,z12,z4,z5]),(0,[z6,z8,z2,z3,z56,z60,z5]),(0,[z6,z169,z8,z2,z3,z135,z4]),(0,[z6,z37,z2,z3,z12,z4,z5]),(0,[z212,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z411,z4,z5]),(0,[z6,z87,z8,z2,z3,z4,z5]),(1,[z6,z87,z8,z3,z125,z4]),(0,[z6,z412,z8,z2,z3,z4,z5])],[(0,[z22,z6,z1,z2,z3,z4,z5]),(0,[z6,z23,z131,z2,z3,z4,z5]),(0,[z302,z6,z8,z2,z3,z4,z5]),(0,[z6,z198,z8,z2,z3,z4,z70]),(0,[z6,z8,z2,z413,z3,z4,z5]),(1,[z6,z8,z2,z3,z414,z4]),(0,[z415,z6,z8,z2,z3,z4,z5])],[(0,[z6,z416,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z139,z4,z5]),(0,[z6,z8,z2,z303,z3,z4,z5]),(0,[z417,z6,z8,z2,z3,z4,z5])],[(0,[z132,z6,z8,z2,z3,z4,z418]),(0,[z6,z419,z8,z2,z3,z4,z5]),(0,[z6,z420,z8,z2,z3,z4,z5]),(1,[z6,z2,z3,z421,z4,z5])],[(1,[z6,z422,z2,z3,z4,z5]),(0,[z6,z87,z163,z2,z3,z4,z5]),(0,[z6,z8,z2,z4,z5,z40,z70])]],
   [[(1,[z30,z8,z318,z3,z4,z5]),(0,[z30,z6,z2,z3,z12,z4,z5]),(0,[z6,z2,z3,z34,z12,z4,z5]),(0,[z175,z6,z8,z2,z181,z4,z5]),(0,[z6,z8,z2,z3,z423,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z424])],[(0,[z6,z8,z2,z425,z3,z4,z5]),(0,[z426,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z427,z4,z5])],[(0,[z428,z6,z8,z2,z3,z4,z5]),(0,[z6,z23,z318,z2,z3,z4,z5])],[(0,[z6,z8,z8,z2,z3,z4,z5]),(0,[z6,z23,z2,z3,z4,z39,z5]),(0,[z6,z8,z2,z429,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z430,z5]),(0,[z6,z8,z2,z3,z4,z5,z88]),(0,[z431,z6,z8,z2,z3,z4,z5])],[(0,[z6,z8,z2,z3,z432,z4,z5]),(0,[z59,z6,z433,z2,z3,z4,z5]),(0,[z11,z6,z23,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z434,z4,z5]),(0,[z6,z8,z2,z435,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z269,z5]),(0,[z6,z8,z2,z3,z414,z4,z5])],[(0,[z436,z6,z8,z2,z3,z4,z5]),(0,[z327,z6,z8,z2,z3,z4,z5]),(0,[z437,z6,z8,z2,z3,z4,z5])],[(0,[z6,z438,z8,z2,z3,z4,z5]),(0,[z59,z6,z8,z2,z3,z227,z5]),(0,[z6,z299,z83,z2,z3,z4,z5]),(0,[z6,z23,z2,z3,z103,z4,z5]),(0,[z439,z6,z8,z2,z3,z4,z5])],[(0,[z6,z8,z2,z3,z4,z440,z5]),(1,[z6,z433,z2,z3,z4,z5]),(0,[z6,z23,z2,z3,z4,z173,z5])]],
   [[(0,[z6,z8,z441,z2,z3,z4,z5]),(0,[z6,z442,z8,z2,z3,z4,z5]),(0,[z443,z6,z8,z2,z3,z4,z5]),(0,[z6,z444,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z371,z4,z5])],[(0,[z6,z445,z8,z2,z3,z4,z5]),(0,[z446,z6,z8,z2,z3,z4,z5]),(0,[z6,z299,z2,z231,z3,z4,z5]),(0,[z6,z23,z2,z3,z4,z5,z116]),(0,[z6,z199,z8,z2,z3,z4,z15]),(1,[z68,z6,z8,z2,z5,z159])],[(0,[z6,z447,z8,z2,z3,z4,z5]),(0,[z448,z6,z8,z2,z3,z4,z5]),(0,[z6,z87,z8,z131,z3,z4,z5]),(1,[z6,z288,z2,z3,z4,z5])],[(0,[z6,z8,z2,z3,z4,z449,z5]),(0,[z6,z8,z2,z3,z450,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z451]),(0,[z6,z8,z2,z3,z452,z4,z5]),(0,[z6,z8,z2,z3,z453,z4,z5]),(0,[z6,z454,z8,z2,z3,z4,z5]),(0,[z6,z455,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z456])],[(0,[z6,z54,z2,z231,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z457])],[(0,[z6,z8,z2,z458,z3,z4,z5]),(0,[z22,z6,z276,z2,z3,z4,z5]),(0,[z175,z6,z8,z2,z34,z4,z5]),(0,[z6,z299,z8,z2,z3,z4,z5]),(0,[z459,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z37,z2,z3,z5,z70])],[(0,[z6,z8,z2,z3,z460,z4,z5]),(0,[z6,z8,z2,z193,z3,z4,z5])],[(0,[z8,z2,z181,z3,z34,z4,z5]),(0,[z6,z8,z2,z3,z461,z4,z5]),(0,[z25,z6,z8,z2,z3,z107,z4]),(0,[z6,z8,z2,z462,z3,z4,z5])]],
   [[(1,[z6,z211,z8,z2,z3,z4]),(0,[z59,z6,z8,z2,z3,z60,z5]),(0,[z6,z83,z2,z3,z4,z15,z5]),(0,[z6,z54,z8,z2,z3,z4,z5]),(0,[z463,z6,z8,z2,z3,z4,z5])],[(0,[z6,z8,z2,z3,z4,z464,z5]),(1,[z6,z8,z2,z3,z4,z226]),(0,[z6,z8,z2,z3,z465,z4,z5]),(0,[z6,z466,z8,z2,z3,z4,z5]),(0,[z6,z8,z467,z2,z3,z4,z5]),(1,[z6,z8,z2,z3,z202,z5])],[(0,[z6,z8,z2,z3,z4,z5,z468]),(0,[z212,z6,z8,z2,z103,z4,z5])],[(0,[z78,z6,z23,z2,z3,z4,z5]),(0,[z35,z6,z23,z2,z3,z4,z5]),(0,[z11,z6,z54,z2,z3,z4,z5]),(0,[z6,z469,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z107,z4,z5])],[(0,[z6,z8,z2,z3,z4,z120,z88]),(0,[z6,z8,z2,z3,z4,z470,z5]),(0,[z6,z8,z2,z3,z4,z5,z70])],[(0,[z6,z8,z2,z3,z471,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z472]),(0,[z6,z23,z2,z113,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z473,z5]),(0,[z6,z198,z8,z2,z3,z4,z15]),(0,[z212,z6,z8,z2,z113,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z474])],[(0,[z6,z8,z2,z3,z4,z475,z5]),(0,[z132,z6,z8,z2,z3,z255,z5]),(0,[z6,z8,z2,z476,z3,z4,z5]),(0,[z477,z6,z8,z2,z3,z4,z5])],[(0,[z6,z8,z2,z3,z4,z478,z5]),(0,[z6,z8,z2,z479,z3,z4,z5]),(0,[z6,z8,z2,z3,z480,z4,z5]),(0,[z481,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z482,z3,z4,z5])]],
   [[(0,[z6,z8,z2,z483,z3,z4,z5]),(1,[z6,z213,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z484,z5]),(0,[z6,z8,z37,z2,z3,z107,z4])],[(0,[z32,z6,z8,z2,z181,z4,z5]),(0,[z6,z8,z210,z2,z3,z4,z5]),(0,[z6,z8,z485,z2,z3,z4,z5]),(0,[z6,z486,z8,z2,z3,z4,z5]),(0,[z6,z8,z487,z2,z3,z4,z5])],[(0,[z6,z276,z2,z231,z3,z4,z5]),(0,[z6,z488,z8,z2,z3,z4,z5]),(1,[z6,z2,z3,z489,z4,z5]),(0,[z6,z2,z3,z489,z4,z227,z5]),(0,[z6,z8,z2,z3,z490,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z491])],[(0,[z6,z8,z2,z3,z4,z5,z492]),(0,[z6,z8,z2,z3,z4,z308,z5])],[(0,[z6,z2,z3,z12,z4,z227,z5]),(0,[z6,z23,z2,z231,z3,z4,z5]),(1,[z6,z493,z2,z3,z4,z5])],[(0,[z78,z6,z8,z131,z2,z3,z4]),(0,[z494,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z495]),(0,[z6,z8,z2,z16,z3,z4,z5]),(0,[z6,z8,z2,z38,z3,z4,z5])],[(0,[z6,z8,z2,z3,z4,z36,z88]),(1,[z6,z299,z231,z3,z4,z5]),(0,[z496,z6,z8,z2,z3,z4,z5])],[(0,[z6,z23,z2,z3,z4,z238,z5]),(0,[z6,z2,z3,z497,z12,z4,z5]),(0,[z6,z8,z2,z3,z4,z498,z5]),(0,[z6,z8,z2,z3,z499,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z500])]],
   [[(0,[z0,z6,z2,z3,z12,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z501]),(0,[z6,z8,z2,z3,z502,z4,z5]),(0,[z6,z8,z2,z3,z497,z4,z5]),(0,[z6,z23,z2,z3,z4,z5,z88]),(0,[z6,z23,z8,z2,z3,z4,z5]),(0,[z6,z199,z2,z3,z12,z4,z5]),(1,[z6,z14,z8,z2,z3,z5]),(0,[z6,z8,z2,z503,z3,z4,z5]),(0,[z6,z412,z2,z3,z4,z5,z26])],[(0,[z30,z8,z318,z2,z3,z4,z5]),(0,[z6,z8,z2,z181,z103,z4,z5]),(0,[z6,z504,z8,z2,z3,z4,z5]),(0,[z212,z6,z8,z42,z3,z4,z5]),(0,[z6,z8,z2,z505,z3,z4,z5]),(0,[z6,z49,z8,z3,z4,z5,z116]),(0,[z6,z92,z8,z2,z38,z3,z4])],[(0,[z506,z6,z8,z2,z3,z4,z5])],[(0,[z22,z8,z276,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z507,z4,z5]),(0,[z508,z6,z8,z2,z3,z4,z5]),(1,[z6,z306,z2,z3,z4,z5]),(0,[z509,z6,z8,z2,z3,z4,z5])],[(0,[z32,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z15,z13,z5]),(0,[z6,z8,z2,z3,z510,z4,z5])],[(0,[z175,z6,z2,z3,z12,z4,z5])],[(0,[z511,z6,z8,z2,z3,z4,z5]),(0,[z6,z433,z8,z2,z3,z4,z5]),(1,[z6,z352,z2,z3,z4,z5]),(0,[z6,z8,z2,z512,z3,z4,z5])],[(1,[z22,z276,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z513,z5]),(0,[z6,z8,z2,z514,z3,z4,z5]),(0,[z6,z23,z2,z181,z3,z4,z5]),(0,[z515,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z516]),(0,[z6,z8,z2,z3,z4,z5,z517])]],
   [[(0,[z6,z8,z2,z518,z3,z4,z5]),(0,[z175,z8,z2,z181,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z26])],[(0,[z22,z6,z8,z2,z3,z4,z5]),(0,[z68,z6,z23,z2,z3,z4,z5]),(0,[z6,z519,z8,z2,z3,z4,z5])],[(0,[z6,z92,z112,z8,z2,z3,z5])],[(0,[z6,z8,z2,z520,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z521]),(0,[z6,z2,z231,z3,z135,z4,z5]),(0,[z6,z522,z8,z2,z3,z4,z5])],[(0,[z6,z8,z2,z3,z155,z4,z5]),(0,[z6,z8,z2,z523,z3,z4,z5]),(0,[z35,z6,z8,z2,z3,z4,z120]),(0,[z6,z198,z2,z3,z12,z4,z5])],[(0,[z6,z524,z8,z2,z3,z4,z5]),(0,[z525,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z107,z5,z70])],[(0,[z0,z22,z8,z2,z3,z4,z5]),(0,[z6,z526,z8,z2,z3,z4,z5]),(0,[z75,z6,z23,z2,z3,z4,z5]),(0,[z6,z527,z8,z2,z3,z4,z5]),(0,[z528,z6,z8,z2,z3,z4,z5])],[(0,[z6,z8,z2,z3,z4,z5,z529]),(0,[z6,z37,z2,z193,z3,z4,z5])]],
   [[(0,[z6,z8,z530,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z531]),(0,[z6,z2,z16,z3,z421,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z532])],[(0,[z6,z8,z2,z3,z533,z4,z5]),(0,[z6,z8,z2,z38,z4,z39,z5])],[(0,[z6,z8,z85,z2,z3,z4,z5]),(0,[z6,z8,z50,z2,z3,z5,z116]),(0,[z6,z8,z131,z2,z3,z4,z88])],[],[(0,[z534,z6,z8,z2,z3,z4,z5]),(0,[z6,z54,z8,z2,z135,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z535])],[(0,[z6,z1,z54,z2,z3,z4,z5]),(0,[z6,z320,z23,z2,z3,z4,z5]),(1,[z6,z2,z3,z12,z4,z5]),(0,[z6,z8,z2,z303,z3,z12,z4]),(0,[z6,z8,z42,z2,z3,z4,z5])],[(0,[z6,z23,z1,z2,z3,z4,z5]),(0,[z132,z6,z8,z318,z3,z4,z5]),(1,[z6,z168,z8,z2,z3,z5]),(0,[z6,z50,z2,z3,z12,z4,z5]),(1,[z6,z69,z2,z3,z4,z5])],[(0,[z6,z54,z276,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z536,z4,z5]),(0,[z6,z8,z2,z3,z537,z4,z5]),(0,[z6,z8,z2,z3,z538,z4,z5])]],
   [[(0,[z6,z8,z2,z3,z539,z4,z5])],[(0,[z6,z8,z540,z2,z3,z4,z5]),(0,[z6,z541,z8,z2,z3,z4,z5]),(0,[z6,z211,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z542,z4,z5])],[(0,[z6,z8,z2,z3,z4,z5,z543]),(1,[z35,z8,z2,z3,z4,z36]),(0,[z6,z23,z2,z38,z3,z4,z5]),(0,[z6,z23,z8,z2,z3,z5,z70]),(0,[z6,z544,z8,z2,z3,z4,z5])],[(0,[z6,z23,z545,z2,z3,z4,z5]),(0,[z6,z23,z2,z321,z3,z4,z5]),(0,[z6,z265,z2,z3,z12,z4,z5]),(0,[z6,z8,z2,z3,z125,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z546])],[(0,[z6,z8,z2,z3,z547,z4,z5]),(0,[z75,z6,z8,z2,z3,z227,z5]),(0,[z6,z8,z548,z2,z3,z4,z5]),(0,[z6,z2,z3,z12,z4,z15,z5]),(0,[z6,z14,z8,z2,z3,z4,z5]),(0,[z6,z8,z131,z2,z3,z125,z4])],[(0,[z6,z8,z2,z3,z549,z4,z5]),(0,[z6,z199,z8,z2,z38,z3,z4]),(0,[z6,z8,z2,z550,z3,z4,z5]),(0,[z6,z8,z551,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z552]),(0,[z553,z6,z8,z2,z3,z4,z5])],[(0,[z35,z6,z340,z2,z3,z4,z5]),(0,[z35,z6,z352,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z140,z4,z5]),(0,[z554,z6,z8,z2,z3,z4,z5]),(0,[z555,z6,z8,z2,z3,z4,z5])],[(0,[z556,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z557]),(0,[z6,z558,z8,z2,z3,z4,z5]),(0,[z6,z8,z559,z2,z3,z4,z5])]],
   [[(0,[z6,z23,z2,z3,z4,z5,z120]),(0,[z6,z190,z2,z3,z12,z4,z5]),(0,[z6,z8,z50,z2,z3,z4,z5]),(0,[z6,z8,z2,z560,z3,z4,z5]),(0,[z6,z561,z8,z2,z3,z4,z5]),(0,[z6,z87,z8,z3,z125,z4,z5])],[(0,[z562,z6,z8,z2,z3,z4,z5]),(0,[z6,z563,z8,z2,z3,z4,z5]),(0,[z6,z83,z2,z3,z135,z4,z5]),(1,[z6,z8,z2,z303,z3,z4]),(0,[z6,z8,z2,z3,z564,z4,z5]),(0,[z565,z6,z8,z2,z3,z4,z5])],[(0,[z6,z8,z2,z3,z4,z566,z5]),(0,[z567,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z568,z2,z3,z4,z5]),(0,[z6,z2,z3,z12,z4,z36,z5]),(0,[z6,z23,z2,z3,z4,z5,z129]),(0,[z6,z8,z2,z569,z3,z4,z5]),(0,[z6,z8,z2,z3,z570,z4,z5]),(0,[z6,z8,z2,z38,z3,z107,z4])],[(0,[z132,z6,z8,z2,z483,z4,z5]),(0,[z6,z112,z8,z2,z3,z238,z5]),(0,[z6,z2,z3,z12,z56,z4,z5]),(0,[z6,z571,z8,z2,z3,z4,z5])],[(0,[z572,z6,z8,z2,z3,z4,z5]),(0,[z6,z573,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z98,z4,z5]),(0,[z6,z23,z2,z344,z3,z4,z5]),(0,[z25,z6,z23,z2,z3,z4,z5]),(0,[z6,z92,z23,z2,z3,z4,z5]),(0,[z574,z6,z2,z3,z12,z4,z5])],[(0,[z6,z8,z340,z2,z3,z4,z5]),(0,[z6,z199,z2,z231,z3,z4,z5]),(0,[z11,z6,z199,z2,z3,z4,z5]),(0,[z6,z23,z2,z3,z4,z5,z26]),(0,[z6,z49,z2,z3,z12,z4,z5]),(0,[z6,z2,z3,z12,z4,z5,z159]),(0,[z6,z92,z8,z37,z2,z3,z4])],[(0,[z6,z8,z2,z3,z4,z575,z5]),(0,[z75,z6,z8,z2,z3,z60,z5]),(0,[z6,z8,z2,z3,z576,z4,z5]),(0,[z366,z6,z23,z2,z3,z4,z5]),(0,[z6,z213,z8,z2,z3,z4,z5]),(1,[z6,z8,z131,z3,z4,z88]),(0,[z6,z2,z3,z4,z5,z104,z26])],[(0,[z6,z23,z276,z2,z3,z4,z5]),(0,[z6,z8,z2,z577,z3,z4,z5]),(0,[z6,z369,z23,z2,z3,z4,z5]),(0,[z578,z6,z8,z2,z3,z4,z5]),(0,[z25,z6,z199,z8,z2,z3,z4]),(0,[z25,z6,z198,z8,z2,z3,z4]),(0,[z6,z8,z2,z3,z579,z4,z5]),(0,[z6,z8,z2,z3,z580,z4,z5]),(0,[z581,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z582,z4,z5])]],
   [[(0,[z6,z8,z2,z583,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z584,z5]),(0,[z6,z8,z2,z3,z585,z4,z5])],[(0,[z132,z6,z8,z2,z3,z4,z5]),(0,[z132,z6,z146,z2,z3,z4,z5]),(0,[z75,z8,z2,z3,z4,z227,z5]),(0,[z6,z199,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z586,z4,z5]),(0,[z6,z198,z8,z2,z38,z3,z4]),(1,[z6,z2,z3,z4,z115,z5])],[(0,[z6,z8,z587,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z125,z4,z36]),(1,[z6,z169,z8,z2,z3,z4]),(1,[z6,z23,z2,z16,z3,z5])],[(0,[z588,z6,z8,z2,z3,z4,z5]),(0,[z6,z589,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z590,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z591])],[(0,[z592,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z593,z4,z5]),(0,[z6,z8,z2,z3,z594,z4,z5]),(0,[z6,z8,z42,z2,z103,z4,z5])],[(0,[z6,z8,z206,z2,z3,z4,z5]),(0,[z6,z8,z2,z34,z103,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z595])],[(0,[z6,z596,z8,z2,z3,z4,z5]),(0,[z175,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z34,z4,z5]),(0,[z6,z8,z2,z597,z3,z4,z5]),(0,[z6,z8,z2,z3,z598,z4,z5]),(0,[z6,z8,z2,z3,z599,z4,z5]),(0,[z6,z8,z2,z3,z4,z600,z5]),(0,[z6,z8,z2,z3,z4,z5,z601]),(0,[z6,z8,z602,z2,z3,z4,z5]),(0,[z6,z603,z8,z2,z3,z4,z5])],[(0,[z6,z23,z85,z2,z3,z4,z5]),(0,[z6,z8,z42,z2,z113,z4,z5]),(0,[z6,z8,z2,z3,z4,z604,z5]),(1,[z6,z110,z2,z3,z4,z5])]],
   [[(0,[z6,z299,z8,z85,z3,z4,z5]),(0,[z6,z605,z8,z2,z3,z4,z5]),(0,[z606,z6,z8,z2,z3,z4,z5])],[(0,[z6,z8,z2,z3,z4,z5,z607]),(0,[z6,z8,z2,z608,z3,z4,z5]),(0,[z6,z8,z2,z3,z609,z4,z5]),(0,[z6,z2,z3,z12,z12,z4,z5]),(0,[z610,z6,z8,z2,z3,z4,z5]),(0,[z6,z611,z8,z2,z3,z4,z5])],[(0,[z6,z8,z2,z31,z3,z4,z5]),(1,[z6,z416,z2,z3,z4,z5]),(0,[z6,z2,z231,z3,z12,z4,z5]),(0,[z6,z23,z42,z2,z3,z4,z5]),(0,[z6,z8,z3,z125,z4,z5,z88])],[(0,[z6,z23,z2,z3,z17,z4,z5]),(0,[z6,z23,z37,z2,z3,z4,z5]),(0,[z612,z6,z8,z2,z3,z4,z5]),(0,[z6,z306,z8,z2,z3,z4,z5])],[(0,[z35,z8,z2,z3,z4,z36,z5]),(0,[z6,z8,z2,z3,z613,z4,z5]),(0,[z6,z8,z2,z3,z614,z4,z5])],[(0,[z615,z6,z8,z2,z3,z4,z5]),(0,[z8,z2,z3,z60,z4,z227,z5]),(0,[z212,z6,z23,z2,z3,z4,z5]),(0,[z6,z87,z23,z2,z3,z4,z5]),(0,[z6,z112,z2,z3,z12,z4,z5]),(0,[z6,z198,z8,z2,z3,z4,z5]),(1,[z6,z2,z3,z4,z5,z221])],[(1,[z6,z8,z2,z3,z4,z418]),(0,[z6,z8,z616,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z617]),(0,[z6,z62,z2,z3,z4,z5,z159])],[(0,[z6,z8,z133,z2,z3,z4,z5]),(0,[z35,z78,z8,z2,z3,z4,z5]),(0,[z6,z83,z8,z231,z3,z4,z5])]],
   [[(1,[z6,z8,z2,z483,z4,z5]),(0,[z6,z8,z2,z3,z4,z618,z5]),(0,[z6,z112,z8,z2,z3,z12,z5])],[(0,[z30,z6,z8,z318,z3,z4,z5]),(0,[z619,z6,z8,z2,z3,z4,z5]),(0,[z6,z87,z422,z2,z3,z4,z5])],[(0,[z620,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z621,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z622,z5]),(0,[z6,z23,z2,z3,z4,z4,z5]),(1,[z212,z6,z8,z103,z4,z5]),(0,[z6,z623,z8,z2,z3,z4,z5]),(1,[z6,z8,z2,z3,z4,z269])],[(0,[z6,z8,z2,z3,z624,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z625]),(0,[z626,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z627,z3,z4,z5]),(0,[z6,z628,z8,z2,z3,z4,z5]),(0,[z6,z545,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z629]),(0,[z630,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z307,z5])],[(0,[z6,z631,z8,z2,z3,z4,z5]),(0,[z6,z416,z2,z3,z4,z227,z5]),(0,[z6,z8,z632,z2,z3,z4,z5]),(0,[z29,z6,z2,z3,z12,z4,z5]),(0,[z6,z2,z303,z3,z12,z4,z5])],[(0,[z633,z6,z8,z2,z3,z4,z5]),(0,[z6,z2,z3,z12,z350,z4,z5]),(0,[z6,z2,z3,z12,z4,z39,z5])],[(1,[z6,z8,z2,z3,z4,z5]),(0,[z6,z634,z8,z2,z3,z4,z5]),(0,[z6,z224,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z635]),(0,[z6,z8,z2,z3,z4,z5,z636])],[(0,[z0,z6,z1,z2,z3,z4,z5]),(0,[z6,z199,z1,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z60,z5,z116]),(0,[z6,z8,z2,z3,z4,z5,z637]),(0,[z6,z8,z2,z638,z3,z4,z5])]],
   [[(0,[z6,z8,z2,z639,z3,z4,z5]),(0,[z132,z6,z23,z2,z3,z4,z5]),(0,[z6,z2,z3,z309,z12,z4,z5]),(0,[z6,z49,z8,z2,z3,z5,z116]),(0,[z6,z8,z2,z3,z421,z4,z5])],[(0,[z6,z640,z8,z2,z3,z4,z5]),(0,[z59,z8,z2,z3,z60,z4,z5]),(0,[z6,z641,z8,z2,z3,z4,z5]),(0,[z6,z199,z8,z37,z2,z3,z4]),(0,[z6,z8,z422,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z70,z26])],[(0,[z642,z6,z8,z2,z3,z4,z5]),(0,[z132,z6,z8,z31,z3,z4,z5]),(1,[z32,z8,z2,z34,z4,z5]),(0,[z6,z8,z2,z3,z4,z227,z5]),(0,[z6,z8,z643,z2,z3,z4,z5])],[(0,[z6,z8,z2,z27,z3,z4,z5]),(0,[z6,z445,z23,z2,z3,z4,z5]),(0,[z6,z2,z3,z12,z4,z5,z116]),(0,[z6,z644,z8,z2,z3,z4,z5])],[(0,[z6,z83,z1,z2,z3,z4,z5]),(0,[z6,z8,z2,z645,z3,z4,z5]),(0,[z6,z8,z2,z3,z646,z4,z5]),(0,[z6,z8,z647,z2,z3,z4,z5]),(1,[z6,z412,z2,z3,z4,z5]),(0,[z6,z110,z8,z2,z3,z4,z5])],[(0,[z6,z8,z2,z3,z4,z5,z418]),(0,[z6,z8,z2,z3,z4,z5,z648]),(0,[z6,z649,z8,z2,z3,z4,z5]),(0,[z650,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z651,z4,z5]),(0,[z6,z8,z2,z3,z414,z4,z159]),(0,[z6,z8,z652,z2,z3,z4,z5])],[],[(0,[z6,z33,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z653,z3,z4,z5]),(0,[z6,z299,z23,z2,z3,z4,z5]),(1,[z6,z8,z2,z3,z4,z315])]],
   [[(0,[z6,z654,z8,z2,z3,z4,z5]),(0,[z6,z8,z655,z2,z3,z4,z5]),(0,[z6,z83,z2,z3,z12,z4,z5]),(0,[z656,z6,z8,z2,z3,z4,z5]),(0,[z91,z6,z8,z2,z3,z4,z5])],[(0,[z657,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z658,z5]),(1,[z6,z8,z2,z16,z17,z5])],[(0,[z6,z2,z3,z12,z60,z4,z5]),(0,[z6,z8,z2,z3,z659,z4,z5]),(0,[z660,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z661,z2,z3,z4,z5])],[(0,[z0,z1,z8,z2,z3,z4,z5]),(0,[z132,z8,z2,z31,z3,z4,z5]),(0,[z6,z466,z23,z2,z3,z4,z5]),(0,[z6,z199,z2,z3,z4,z5,z129]),(1,[z6,z2,z274,z3,z4,z5]),(0,[z6,z662,z8,z2,z3,z4,z5])],[(0,[z30,z6,z8,z2,z3,z4,z5]),(0,[z663,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z227,z5,z116]),(0,[z11,z6,z2,z3,z4,z15,z5]),(0,[z6,z8,z2,z3,z4,z5,z664]),(0,[z6,z8,z665,z2,z3,z4,z5]),(0,[z6,z50,z2,z274,z3,z4,z5])],[(0,[z574,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z5]),(0,[z6,z8,z2,z3,z666,z4,z5]),(0,[z6,z8,z272,z2,z3,z4,z5]),(0,[z6,z198,z8,z37,z2,z3,z4]),(0,[z25,z6,z8,z2,z38,z4,z5])],[(0,[z6,z8,z2,z3,z667,z4,z5]),(0,[z1,z8,z276,z2,z3,z4,z5]),(1,[z6,z8,z2,z3,z255,z5]),(1,[z6,z199,z2,z3,z4,z129]),(0,[z6,z8,z2,z3,z668,z4,z5]),(0,[z6,z49,z8,z2,z3,z4,z5])],[(0,[z6,z23,z2,z31,z3,z4,z5]),(0,[z78,z6,z8,z2,z3,z4,z120]),(0,[z6,z23,z8,z2,z16,z3,z5]),(0,[z6,z669,z8,z2,z3,z4,z5])]],
   [[(0,[z0,z6,z276,z2,z3,z4,z5]),(0,[z6,z199,z276,z2,z3,z4,z5]),(0,[z6,z2,z181,z3,z12,z4,z5]),(0,[z670,z6,z8,z2,z3,z4,z5]),(0,[z68,z25,z6,z8,z2,z4,z5]),(0,[z6,z8,z671,z2,z3,z4,z5])],[(0,[z672,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z673,z4,z5]),(0,[z6,z674,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z675,z5])],[(0,[z6,z8,z2,z3,z676,z4,z5])],[(0,[z677,z6,z8,z2,z3,z4,z5]),(0,[z6,z23,z2,z3,z107,z4,z5]),(0,[z6,z8,z2,z3,z4,z678,z5]),(0,[z6,z679,z8,z2,z3,z4,z5]),(0,[z680,z6,z8,z2,z3,z4,z5])],[(0,[z6,z8,z2,z113,z34,z4,z5]),(0,[z6,z8,z681,z2,z3,z4,z5]),(0,[z6,z23,z2,z3,z4,z5,z70]),(0,[z6,z2,z3,z12,z4,z5,z21]),(0,[z6,z8,z2,z3,z4,z5,z682]),(0,[z6,z8,z2,z3,z4,z683,z5])],[(0,[z6,z83,z276,z2,z3,z4,z5]),(0,[z684,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z685,z4,z5]),(0,[z59,z6,z2,z3,z12,z4,z5])],[(0,[z686,z6,z8,z2,z3,z4,z5]),(0,[z687,z6,z8,z2,z3,z4,z5]),(0,[z212,z6,z493,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z315])],[(0,[z688,z6,z8,z2,z3,z4,z5]),(1,[z6,z62,z2,z3,z4,z5])]],
   [[(0,[z132,z30,z8,z2,z3,z4,z5]),(0,[z132,z6,z8,z2,z3,z203,z5]),(0,[z689,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z690,z2,z3,z4,z5]),(0,[z6,z23,z199,z2,z3,z4,z5]),(0,[z6,z8,z691,z2,z3,z4,z5]),(0,[z6,z8,z113,z3,z103,z4,z5]),(0,[z6,z8,z2,z3,z692,z4,z5])],[(0,[z693,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z694,z5]),(0,[z6,z2,z3,z12,z4,z238,z5]),(0,[z6,z8,z2,z3,z4,z5,z695])],[(0,[z6,z23,z23,z2,z3,z4,z5])],[(0,[z6,z318,z2,z3,z12,z4,z5]),(0,[z6,z8,z696,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z697,z5]),(0,[z6,z698,z8,z2,z3,z4,z5])],[(0,[z6,z1,z2,z3,z135,z4,z5]),(0,[z6,z8,z2,z3,z489,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z699]),(0,[z6,z288,z8,z2,z3,z4,z5])],[(0,[z6,z8,z2,z700,z3,z4,z5]),(0,[z6,z23,z2,z16,z3,z4,z5]),(1,[z6,z23,z2,z3,z238,z5]),(0,[z6,z8,z2,z3,z701,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z702])],[(0,[z32,z6,z23,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z703]),(0,[z102,z6,z8,z2,z3,z4,z5]),(0,[z6,z112,z8,z2,z3,z4,z5]),(0,[z6,z8,z493,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z5,z704])],[(0,[z705,z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z706,z2,z3,z4,z5]),(0,[z6,z23,z2,z3,z4,z227,z5])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z55,z1,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z707,z4]),(0,[z6,z2,z3,z4,z5,z708]),(0,[z6,z8,z2,z3,z709,z4]),(0,[z6,z2,z27,z4,z5,z148])],[(0,[z6,z8,z3,z710,z4,z5]),(0,[z6,z2,z711,z3,z4,z5]),(0,[z212,z6,z8,z103,z4,z5]),(0,[z6,z8,z2,z3,z4,z712])],[(0,[z8,z2,z713,z34,z4,z5]),(0,[z6,z306,z50,z3,z56,z5]),(0,[z6,z110,z2,z16,z3,z5]),(0,[z6,z8,z2,z292,z4,z39]),(0,[z91,z6,z8,z2,z3,z107]),(0,[z6,z92,z37,z2,z193,z3])],[(0,[z6,z714,z2,z3,z4,z5]),(0,[z6,z2,z3,z12,z542,z5]),(0,[z6,z87,z8,z3,z715,z4]),(0,[z6,z716,z2,z3,z4,z5])],[(0,[z6,z8,z2,z3,z717,z5]),(0,[z6,z718,z2,z3,z4,z5]),(0,[z6,z23,z131,z3,z4,z88]),(0,[z6,z112,z2,z3,z421,z5]),(0,[z68,z6,z8,z2,z269,z159]),(0,[z68,z6,z62,z2,z5,z159]),(0,[z6,z92,z8,z719,z2,z3])],[(0,[z6,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z720,z5]),(0,[z6,z54,z2,z27,z4,z5])],[(0,[z6,z8,z2,z721,z4,z5]),(0,[z6,z2,z3,z722,z4,z5]),(0,[z6,z2,z3,z53,z12,z4]),(0,[z6,z8,z2,z3,z715,z4]),(0,[z25,z6,z2,z4,z104,z26]),(0,[z6,z8,z2,z4,z5,z723])],[(0,[z6,z596,z2,z3,z12,z5]),(0,[z6,z83,z711,z3,z4,z5]),(0,[z6,z168,z169,z8,z2,z3]),(0,[z6,z2,z3,z371,z5,z104])]],
   [[(0,[z6,z23,z2,z3,z154,z5]),(0,[z6,z14,z2,z231,z3,z5]),(0,[z6,z8,z2,z3,z4,z724]),(0,[z6,z14,z2,z3,z5,z129]),(0,[z6,z725,z2,z3,z4,z5]),(0,[z6,z726,z2,z3,z4,z5])],[(0,[z6,z8,z2,z727,z4,z5]),(0,[z32,z8,z2,z34,z4,z5]),(0,[z59,z2,z3,z12,z60,z5]),(0,[z6,z163,z2,z3,z4,z5]),(0,[z6,z23,z2,z3,z161,z5]),(0,[z728,z23,z2,z3,z4,z5])],[(0,[z68,z6,z23,z2,z3,z269])],[(0,[z0,z729,z2,z3,z4,z5]),(0,[z6,z8,z730,z3,z4,z5]),(0,[z6,z83,z365,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z731]),(0,[z6,z112,z8,z2,z3,z315]),(0,[z6,z2,z3,z732,z4,z5])],[(0,[z6,z133,z2,z3,z4,z226]),(0,[z6,z2,z3,z733,z4,z5]),(0,[z443,z8,z2,z181,z4,z5]),(0,[z6,z8,z734,z3,z4,z5]),(0,[z6,z8,z2,z3,z735,z5])],[(0,[z132,z8,z31,z3,z4,z226]),(0,[z6,z2,z3,z4,z736,z5]),(0,[z6,z14,z2,z27,z3,z5]),(0,[z6,z49,z8,z3,z5,z116]),(0,[z6,z2,z3,z150,z4,z221])],[(0,[z6,z8,z2,z3,z4,z737]),(0,[z6,z8,z2,z3,z738,z5]),(0,[z65,z6,z23,z2,z3,z5]),(0,[z6,z8,z711,z3,z4,z5]),(0,[z319,z6,z2,z135,z4,z5]),(0,[z68,z6,z23,z2,z3,z5]),(0,[z6,z2,z3,z739,z4,z5]),(0,[z8,z2,z3,z4,z5,z740]),(0,[z6,z8,z2,z3,z4,z315])],[(0,[z132,z8,z31,z3,z203,z5]),(0,[z6,z8,z741,z3,z4,z5]),(0,[z6,z742,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z743,z5]),(0,[z6,z744,z2,z3,z4,z5])]],
   [[(0,[z6,z168,z2,z3,z12,z5]),(0,[z6,z23,z8,z2,z3,z21]),(0,[z6,z2,z193,z3,z4,z5])],[(0,[z6,z8,z194,z2,z3,z4]),(0,[z75,z416,z2,z3,z227,z5])],[(0,[z6,z8,z2,z155,z4,z226]),(0,[z6,z8,z2,z3,z745,z5]),(0,[z6,z8,z2,z3,z4,z746]),(0,[z6,z8,z3,z747,z4,z5]),(0,[z6,z2,z3,z4,z748,z5])],[(0,[z6,z749,z2,z3,z4,z5]),(0,[z302,z6,z23,z2,z3,z5]),(0,[z6,z23,z2,z303,z3,z12]),(0,[z68,z25,z6,z8,z2,z107])],[(0,[z494,z276,z2,z3,z4,z5]),(0,[z6,z23,z2,z3,z4,z418]),(0,[z91,z6,z23,z2,z4,z5]),(0,[z6,z198,z14,z2,z3,z5])],[(0,[z6,z146,z2,z3,z255,z5]),(0,[z6,z23,z2,z3,z432,z5]),(0,[z6,z8,z2,z3,z750,z5]),(0,[z6,z751,z8,z2,z3,z5]),(0,[z6,z8,z752,z3,z4,z5]),(0,[z6,z753,z2,z3,z4,z5]),(0,[z6,z8,z2,z754,z4,z5]),(0,[z6,z199,z2,z3,z4,z129]),(0,[z6,z8,z131,z3,z715,z4]),(0,[z6,z755,z2,z3,z4,z5])],[(0,[z11,z6,z2,z140,z4,z5]),(0,[z6,z8,z3,z756,z5,z116]),(0,[z6,z8,z2,z3,z756,z5])],[(0,[z68,z6,z23,z2,z3,z315]),(0,[z6,z8,z747,z103,z4,z5]),(0,[z6,z757,z2,z3,z4,z5])]],
   [[(0,[z6,z758,z2,z3,z4,z5]),(0,[z6,z23,z2,z3,z4,z269]),(0,[z6,z131,z3,z12,z4,z88]),(0,[z6,z2,z3,z759,z4,z5])],[(0,[z6,z141,z231,z3,z4,z5]),(0,[z6,z760,z2,z3,z4,z5]),(0,[z6,z8,z2,z4,z5,z761]),(0,[z6,z762,z2,z3,z4,z5])],[(0,[z6,z763,z2,z3,z4,z5]),(0,[z6,z8,z3,z4,z756,z5]),(0,[z91,z6,z8,z2,z107,z4])],[(0,[z6,z210,z2,z3,z4,z5]),(0,[z6,z410,z23,z2,z3,z5]),(0,[z6,z8,z764,z2,z3,z4]),(0,[z212,z6,z8,z747,z4,z5])],[(0,[z75,z2,z3,z489,z227,z5]),(0,[z6,z23,z2,z3,z590,z5]),(0,[z6,z2,z3,z765,z4,z5])],[(0,[z6,z23,z2,z3,z4,z766]),(0,[z6,z8,z2,z3,z4,z767]),(0,[z768,z8,z2,z3,z4,z5]),(0,[z6,z92,z8,z37,z2,z3])],[(0,[z252,z276,z2,z3,z4,z5]),(0,[z6,z168,z2,z231,z3,z5]),(0,[z6,z62,z2,z3,z150,z4]),(0,[z25,z6,z8,z2,z4,z26])],[(0,[z6,z769,z2,z3,z4,z5]),(0,[z6,z23,z2,z3,z5,z21]),(0,[z6,z2,z3,z12,z150,z4]),(0,[z6,z2,z3,z770,z4,z5]),(0,[z68,z6,z8,z2,z150,z4]),(0,[z6,z288,z2,z3,z107,z70])]],
   [[(0,[z6,z8,z2,z771,z4,z5]),(0,[z6,z772,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z773,z5])],[(0,[z6,z8,z2,z774,z3,z4]),(0,[z6,z198,z2,z3,z15,z13]),(0,[z6,z775,z2,z3,z4,z5]),(0,[z6,z8,z3,z715,z4,z5]),(0,[z6,z8,z2,z150,z17,z4])],[(0,[z670,z1,z2,z3,z4,z5]),(0,[z6,z8,z2,z4,z5,z776]),(0,[z8,z2,z3,z4,z36,z777]),(0,[z11,z6,z2,z778,z4,z5]),(0,[z6,z224,z272,z3,z4,z5]),(0,[z6,z8,z2,z4,z39,z315]),(0,[z68,z6,z8,z2,z150,z159])],[(0,[z6,z486,z231,z3,z4,z5]),(0,[z6,z2,z778,z135,z4,z5]),(0,[z6,z412,z37,z2,z3,z4])],[(0,[z6,z8,z2,z3,z4,z779]),(0,[z6,z169,z2,z3,z12,z4]),(0,[z6,z23,z2,z3,z238,z5]),(0,[z6,z780,z2,z3,z4,z5])],[(0,[z6,z8,z2,z3,z4,z781]),(0,[z78,z8,z2,z3,z4,z777]),(0,[z6,z782,z8,z2,z3,z4]),(0,[z6,z87,z8,z653,z3,z4]),(0,[z6,z2,z303,z193,z3,z4])],[(0,[z729,z276,z2,z3,z4,z5]),(0,[z6,z133,z2,z3,z255,z5]),(0,[z6,z2,z3,z12,z4,z783]),(0,[z6,z2,z3,z4,z5,z784]),(0,[z25,z6,z8,z2,z4,z532])],[(0,[z6,z2,z3,z785,z4,z5]),(0,[z32,z33,z2,z34,z4,z5]),(0,[z6,z786,z2,z3,z4,z5]),(0,[z6,z2,z3,z787,z4,z5]),(0,[z6,z788,z2,z3,z4,z5]),(0,[z6,z23,z2,z16,z17,z5]),(0,[z91,z6,z23,z2,z3,z5]),(0,[z6,z8,z2,z371,z39,z5])]],
   [[(0,[z6,z2,z3,z12,z575,z5]),(0,[z6,z23,z2,z3,z5,z248]),(0,[z6,z8,z2,z3,z4,z723])],[(0,[z6,z54,z2,z778,z4,z5]),(0,[z6,z2,z3,z12,z4,z21])],[(0,[z6,z8,z3,z4,z5,z789]),(0,[z6,z2,z3,z307,z13,z5]),(0,[z6,z62,z2,z16,z3,z5])],[(0,[z68,z6,z23,z2,z321,z5]),(0,[z8,z2,z3,z4,z5,z790])],[(0,[z6,z23,z2,z3,z255,z5]),(0,[z6,z8,z2,z3,z203,z418]),(0,[z6,z49,z23,z3,z5,z116])],[(0,[z6,z2,z3,z791,z4,z5]),(0,[z8,z2,z3,z4,z5,z792]),(0,[z6,z780,z2,z3,z4,z315])],[(0,[z6,z793,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z794,z5]),(0,[z91,z6,z23,z2,z5,z70])],[(0,[z6,z2,z303,z3,z497,z4])]],
   [[(0,[z6,z795,z8,z2,z3,z4]),(0,[z78,z2,z3,z12,z4,z120]),(0,[z6,z2,z3,z796,z4,z5]),(0,[z6,z797,z2,z3,z4,z5]),(0,[z6,z8,z50,z3,z756,z5]),(0,[z6,z2,z3,z4,z798,z5]),(0,[z6,z799,z2,z3,z4,z5])],[(0,[z6,z8,z2,z3,z800,z5]),(0,[z6,z801,z2,z3,z4,z5])],[(0,[z6,z8,z2,z3,z4,z802]),(0,[z59,z8,z2,z3,z60,z5]),(0,[z6,z803,z2,z3,z4,z5]),(0,[z6,z8,z2,z17,z5,z248])],[(0,[z6,z194,z2,z3,z12,z4]),(0,[z6,z804,z2,z3,z4,z5]),(0,[z6,z466,z23,z2,z3,z70]),(0,[z6,z8,z2,z3,z805,z4]),(0,[z6,z2,z3,z12,z4,z806]),(1,[z6,z8,z2,z4,z723])],[(0,[z6,z807,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z808]),(0,[z6,z809,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z810])],[(0,[z6,z8,z2,z3,z811,z5]),(0,[z6,z2,z155,z12,z4,z5]),(0,[z6,z8,z2,z3,z4,z812]),(0,[z6,z23,z2,z5,z40,z70]),(0,[z6,z49,z69,z3,z5,z116]),(0,[z68,z6,z8,z2,z315,z159]),(0,[z25,z6,z8,z2,z371,z5])],[(0,[z6,z8,z2,z3,z813,z4]),(0,[z6,z8,z2,z3,z4,z814]),(0,[z6,z2,z815,z3,z4,z5]),(0,[z553,z8,z2,z3,z227,z5]),(0,[z6,z8,z2,z816,z3,z4]),(0,[z6,z817,z2,z3,z4,z5]),(0,[z6,z8,z2,z747,z4,z5]),(0,[z6,z62,z2,z3,z414,z4])],[(0,[z6,z2,z303,z3,z12,z4]),(1,[z6,z2,z3,z4,z818]),(0,[z6,z819,z2,z3,z4,z5])]],
   [[(0,[z6,z8,z2,z3,z4,z820]),(0,[z6,z23,z2,z3,z297,z5])],[(0,[z6,z14,z1,z2,z3,z5]),(0,[z6,z23,z2,z3,z12,z5]),(0,[z6,z2,z3,z4,z798,z315])],[(0,[z78,z8,z405,z2,z3,z4]),(0,[z106,z8,z2,z3,z4,z120]),(0,[z6,z8,z2,z3,z53,z4]),(0,[z6,z821,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z818]),(0,[z68,z6,z8,z2,z414,z159]),(0,[z68,z6,z8,z2,z3,z150])],[(0,[z6,z822,z2,z3,z4,z5]),(0,[z35,z23,z2,z3,z4,z36]),(0,[z6,z8,z2,z3,z371,z70]),(0,[z6,z8,z719,z2,z3,z70])],[(0,[z6,z823,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z824,z5]),(0,[z6,z23,z2,z162,z3,z5]),(0,[z6,z92,z23,z37,z2,z3]),(0,[z6,z2,z3,z4,z818,z129]),(0,[z6,z8,z2,z4,z39,z723])],[(0,[z6,z8,z825,z3,z4,z5]),(0,[z6,z826,z2,z3,z4,z5]),(1,[z8,z2,z3,z4,z777]),(0,[z8,z2,z3,z827,z4,z5]),(0,[z6,z85,z711,z3,z4,z5]),(0,[z25,z6,z23,z2,z4,z26]),(0,[z6,z112,z2,z3,z828,z5])],[(0,[z6,z829,z2,z3,z4,z5]),(0,[z6,z2,z3,z414,z12,z4]),(0,[z6,z8,z2,z3,z830,z5]),(0,[z6,z92,z8,z2,z3,z702])],[(0,[z831,z6,z8,z2,z4,z5]),(0,[z25,z6,z126,z8,z2,z4])]],
   [[(0,[z6,z301,z231,z3,z4,z5]),(0,[z6,z23,z2,z3,z646,z5]),(0,[z6,z198,z2,z303,z3,z4])],[(0,[z6,z83,z85,z3,z4,z5]),(0,[z91,z6,z23,z8,z2,z5]),(0,[z6,z49,z3,z12,z5,z116]),(0,[z6,z2,z3,z832,z4,z5])],[(0,[z729,z8,z2,z3,z4,z5]),(0,[z6,z146,z2,z483,z4,z5]),(0,[z32,z2,z34,z12,z4,z5]),(0,[z6,z2,z3,z833,z4,z5]),(0,[z6,z8,z2,z3,z834,z5])],[(0,[z364,z6,z2,z135,z4,z5]),(0,[z6,z711,z231,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z835]),(0,[z6,z23,z2,z638,z3,z5]),(0,[z6,z23,z2,z4,z5,z40]),(0,[z6,z2,z3,z4,z5,z836]),(0,[z6,z2,z3,z837,z4,z5])],[(0,[z6,z838,z2,z3,z4,z5]),(0,[z6,z839,z2,z3,z4,z5]),(0,[z6,z2,z3,z840,z5,z70]),(0,[z6,z50,z3,z12,z56,z5]),(0,[z6,z8,z2,z38,z586,z4])],[(0,[z6,z841,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z139,z5]),(0,[z6,z8,z42,z113,z4,z5])],[(0,[z6,z842,z2,z3,z4,z5]),(0,[z8,z318,z843,z3,z4,z5])],[(1,[z8,z843,z3,z4,z5]),(0,[z302,z6,z14,z2,z3,z5]),(0,[z6,z844,z2,z3,z4,z5])]],
   [[(0,[z6,z146,z2,z3,z4,z5]),(0,[z6,z8,z2,z845,z4,z5]),(0,[z59,z210,z2,z3,z60,z5]),(0,[z11,z6,z2,z135,z4,z5]),(0,[z6,z8,z2,z3,z150,z4])],[(0,[z6,z846,z2,z3,z4,z5]),(0,[z11,z6,z168,z2,z135,z5]),(1,[z91,z6,z23,z2,z5]),(0,[z6,z8,z2,z847,z4,z5])],[(0,[z6,z83,z272,z3,z4,z5]),(0,[z11,z6,z2,z303,z3,z4]),(0,[z6,z23,z2,z38,z4,z39]),(0,[z6,z2,z3,z848,z4,z5]),(0,[z6,z190,z3,z4,z308,z5]),(0,[z6,z2,z3,z12,z107,z70])],[(0,[z6,z8,z2,z3,z849,z5]),(0,[z6,z23,z2,z3,z348,z5]),(0,[z6,z2,z3,z12,z172,z5]),(1,[z6,z23,z2,z3,z315]),(0,[z6,z2,z3,z850,z4,z5]),(0,[z6,z8,z3,z125,z715,z4]),(0,[z6,z8,z719,z2,z3,z107])],[(0,[z6,z2,z3,z12,z4,z226]),(0,[z6,z851,z2,z3,z4,z5]),(0,[z6,z2,z303,z3,z350,z4]),(0,[z6,z8,z2,z3,z480,z70])],[(0,[z6,z8,z2,z852,z4,z5]),(0,[z6,z23,z2,z3,z5,z356]),(0,[z6,z92,z23,z2,z3,z5]),(0,[z6,z8,z2,z853,z4,z5])],[(0,[z6,z8,z2,z3,z4,z854]),(0,[z6,z2,z3,z12,z203,z5]),(0,[z6,z8,z843,z3,z4,z5]),(0,[z6,z855,z2,z3,z4,z5]),(0,[z6,z8,z3,z4,z5,z856]),(0,[z6,z199,z2,z3,z4,z635]),(0,[z6,z2,z3,z4,z15,z393])],[(0,[z6,z168,z1,z2,z3,z5]),(0,[z6,z8,z2,z3,z4,z783]),(0,[z6,z112,z8,z2,z3,z21])]],
   [[(0,[z6,z8,z2,z3,z857,z5]),(0,[z6,z858,z8,z2,z3,z5]),(1,[z25,z6,z8,z2,z371]),(0,[z25,z6,z8,z2,z371,z4]),(0,[z6,z2,z3,z4,z859,z5])],[(0,[z6,z133,z2,z3,z4,z418]),(0,[z6,z860,z2,z3,z4,z5]),(0,[z68,z6,z23,z2,z140,z5]),(0,[z861,z8,z2,z3,z4,z5]),(0,[z6,z117,z2,z16,z17,z5])],[(0,[z6,z8,z2,z3,z4,z862]),(0,[z132,z8,z31,z3,z4,z418]),(0,[z6,z8,z863,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z21]),(0,[z6,z112,z2,z303,z3,z12]),(0,[z6,z8,z2,z4,z5,z864])],[(0,[z6,z8,z2,z3,z865,z5]),(0,[z6,z133,z2,z483,z4,z5]),(0,[z32,z206,z2,z34,z4,z5]),(0,[z6,z8,z2,z3,z4,z866]),(0,[z6,z2,z3,z867,z4,z5]),(0,[z6,z868,z2,z3,z4,z5])],[(0,[z35,z8,z2,z3,z4,z777]),(0,[z6,z8,z2,z3,z4,z869]),(0,[z6,z92,z23,z2,z38,z3]),(0,[z6,z870,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z871,z5])],[(0,[z6,z872,z2,z3,z4,z5])],[(0,[z6,z2,z3,z785,z203,z5]),(0,[z6,z8,z873,z3,z4,z5]),(0,[z6,z176,z8,z3,z125,z4]),(0,[z6,z2,z303,z3,z207,z4]),(0,[z6,z2,z3,z4,z5,z874])],[(0,[z6,z8,z2,z155,z4,z418]),(0,[z8,z2,z843,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z875]),(0,[z6,z8,z2,z3,z876,z5]),(0,[z6,z2,z3,z877,z4,z5]),(0,[z6,z168,z8,z2,z3,z53]),(0,[z6,z412,z2,z3,z371,z5])]],
   [[(0,[z6,z54,z2,z518,z4,z5]),(0,[z6,z878,z2,z3,z4,z5]),(0,[z6,z879,z2,z3,z4,z5]),(0,[z6,z880,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z881]),(0,[z6,z8,z2,z5,z882,z159]),(0,[z6,z883,z2,z3,z4,z5])],[(0,[z6,z133,z2,z3,z4,z5]),(0,[z6,z8,z2,z884,z4,z5]),(0,[z6,z8,z2,z3,z4,z885]),(0,[z6,z23,z2,z483,z4,z5]),(0,[z6,z2,z886,z3,z4,z5]),(0,[z78,z8,z2,z3,z4,z120]),(0,[z6,z85,z3,z4,z308,z5]),(0,[z6,z369,z8,z2,z3,z70]),(0,[z6,z887,z8,z2,z3,z5])],[],[(0,[z8,z2,z3,z713,z4,z5]),(0,[z6,z888,z2,z3,z4,z5]),(0,[z6,z8,z889,z3,z4,z5]),(0,[z6,z8,z2,z38,z3,z371])],[(0,[z6,z8,z2,z3,z4,z806]),(0,[z6,z8,z2,z3,z890,z5]),(0,[z6,z2,z3,z891,z4,z5]),(0,[z6,z892,z2,z3,z4,z5]),(0,[z6,z8,z42,z747,z4,z5]),(0,[z6,z8,z2,z16,z3,z150]),(0,[z6,z2,z3,z893,z421,z4])],[(0,[z132,z211,z8,z31,z3,z4]),(0,[z6,z894,z2,z3,z4,z5]),(0,[z6,z2,z3,z4,z307,z5]),(0,[z91,z6,z8,z2,z4,z39])],[(0,[z6,z8,z2,z895,z4,z5]),(0,[z6,z896,z2,z3,z4,z5]),(1,[z6,z2,z3,z828,z5])],[(0,[z6,z23,z2,z3,z4,z5]),(0,[z8,z2,z3,z60,z897,z5]),(0,[z6,z87,z8,z3,z125,z4]),(0,[z6,z2,z898,z3,z4,z5])]],
   [[(0,[z6,z899,z2,z3,z4,z5]),(0,[z75,z8,z2,z3,z227,z5]),(0,[z6,z2,z303,z250,z3,z4]),(0,[z6,z198,z2,z3,z4,z15]),(0,[z6,z900,z2,z3,z4,z5]),(0,[z68,z6,z8,z2,z5,z882]),(0,[z6,z8,z2,z3,z414,z4]),(0,[z6,z2,z3,z107,z307,z70])],[(0,[z6,z901,z2,z3,z4,z5])],[(0,[z6,z8,z2,z3,z902,z5]),(0,[z6,z8,z2,z3,z4,z903]),(0,[z6,z2,z3,z421,z4,z5]),(0,[z6,z23,z2,z250,z3,z5]),(0,[z6,z904,z2,z3,z4,z5]),(0,[z6,z905,z2,z3,z4,z5])],[(0,[z6,z169,z1,z2,z3,z4]),(0,[z6,z8,z2,z3,z906,z5]),(0,[z32,z23,z2,z34,z4,z5]),(0,[z6,z907,z2,z3,z4,z5]),(0,[z6,z422,z2,z3,z4,z5]),(0,[z6,z2,z27,z778,z4,z5]),(0,[z6,z2,z3,z12,z13,z5]),(0,[z91,z6,z8,z2,z107,z70])],[(0,[z30,z8,z318,z3,z4,z5]),(0,[z6,z2,z3,z908,z255,z5]),(0,[z6,z2,z3,z909,z4,z5])],[(0,[z6,z14,z276,z2,z3,z5]),(0,[z6,z2,z483,z12,z4,z5]),(0,[z6,z910,z8,z2,z3,z5]),(0,[z6,z23,z2,z3,z4,z731]),(0,[z6,z369,z2,z3,z4,z257]),(0,[z6,z2,z3,z4,z5,z911])],[(0,[z6,z33,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z912]),(0,[z35,z340,z2,z3,z4,z36]),(0,[z35,z352,z2,z3,z4,z36]),(0,[z6,z374,z2,z3,z12,z5]),(0,[z6,z168,z2,z27,z3,z5]),(0,[z6,z23,z734,z3,z4,z5]),(0,[z6,z58,z2,z3,z12,z5]),(0,[z6,z2,z3,z913,z4,z5]),(0,[z6,z914,z2,z3,z4,z5])],[(0,[z8,z2,z3,z4,z777,z120]),(0,[z6,z915,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z916,z4]),(0,[z6,z2,z3,z12,z4,z917]),(0,[z68,z6,z2,z12,z5,z159])]],
   [[(0,[z6,z23,z2,z3,z4,z315]),(0,[z6,z2,z3,z309,z4,z21]),(0,[z6,z918,z2,z3,z4,z5]),(0,[z6,z919,z2,z3,z4,z5])],[(0,[z6,z2,z3,z4,z920,z5]),(0,[z6,z92,z110,z37,z2,z3])],[(0,[z132,z8,z31,z3,z255,z5]),(0,[z6,z822,z2,z3,z203,z5]),(0,[z921,z8,z2,z3,z4,z5]),(0,[z6,z2,z16,z3,z796,z5]),(0,[z6,z8,z2,z38,z19,z4])],[(0,[z6,z433,z2,z3,z4,z5]),(0,[z6,z922,z8,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z923]),(0,[z6,z8,z2,z3,z4,z924]),(0,[z6,z23,z194,z2,z3,z4]),(0,[z6,z8,z2,z3,z4,z925]),(0,[z6,z2,z3,z12,z371,z5])],[(0,[z6,z8,z2,z3,z4,z926]),(0,[z6,z927,z2,z3,z4,z5]),(0,[z6,z928,z2,z3,z4,z5]),(0,[z6,z199,z2,z3,z4,z699]),(0,[z25,z6,z8,z2,z4,z315])],[(0,[z6,z929,z2,z3,z4,z5]),(0,[z6,z2,z12,z4,z5,z40]),(0,[z25,z6,z8,z2,z401,z4]),(0,[z6,z930,z2,z3,z4,z5]),(0,[z68,z6,z8,z2,z5,z159])],[(0,[z6,z8,z2,z3,z931,z5]),(0,[z6,z8,z932,z3,z4,z5]),(0,[z6,z8,z2,z3,z933,z5]),(0,[z6,z2,z3,z4,z5,z934]),(0,[z6,z8,z2,z3,z4,z935]),(0,[z6,z936,z2,z3,z4,z5])],[(0,[z6,z8,z2,z155,z255,z5]),(0,[z6,z937,z2,z3,z4,z5]),(0,[z6,z142,z344,z3,z4,z5]),(0,[z6,z23,z752,z3,z4,z5]),(0,[z6,z49,z8,z3,z756,z5]),(0,[z6,z938,z2,z3,z421,z4]),(0,[z6,z412,z2,z3,z4,z70])]],
   [[(1,[z6,z8,z3,z715,z4]),(0,[z91,z6,z2,z4,z307,z5])],[(0,[z6,z2,z3,z939,z4,z5]),(0,[z6,z8,z2,z483,z203,z5]),(0,[z6,z8,z2,z3,z940,z4]),(0,[z6,z8,z37,z2,z3,z500])],[],[(0,[z6,z941,z2,z3,z4,z5]),(0,[z6,z563,z23,z2,z3,z5]),(0,[z11,z6,z2,z53,z135,z4]),(0,[z302,z6,z2,z303,z3,z4]),(0,[z6,z8,z2,z3,z107,z70])],[(0,[z6,z211,z8,z2,z3,z4]),(0,[z6,z8,z3,z715,z4,z88])],[(0,[z6,z942,z2,z3,z4,z5]),(0,[z6,z169,z2,z231,z3,z4]),(0,[z68,z6,z8,z2,z140,z5]),(0,[z6,z943,z2,z3,z4,z5]),(0,[z6,z944,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z202,z5])],[(0,[z6,z945,z2,z3,z4,z5]),(0,[z6,z8,z2,z713,z4,z5]),(0,[z946,z8,z2,z3,z4,z5]),(0,[z6,z2,z3,z12,z4,z947]),(0,[z6,z2,z3,z12,z4,z948])],[(0,[z6,z8,z2,z3,z203,z5]),(0,[z6,z146,z2,z3,z203,z5]),(0,[z6,z2,z949,z3,z4,z5]),(0,[z6,z23,z2,z3,z218,z5]),(0,[z6,z466,z2,z3,z4,z173]),(0,[z6,z950,z8,z2,z3,z4]),(0,[z6,z2,z951,z3,z12,z4])]],
   [[(0,[z6,z369,z23,z2,z3,z70]),(0,[z6,z112,z2,z3,z12,z5])],[(0,[z6,z8,z2,z3,z4,z952]),(0,[z6,z23,z2,z3,z5,z70]),(0,[z554,z6,z23,z2,z3,z5]),(0,[z6,z953,z2,z3,z4,z5]),(0,[z25,z6,z8,z2,z3,z371])],[(1,[z6,z2,z778,z4,z5]),(0,[z6,z169,z2,z27,z3,z4]),(0,[z6,z23,z2,z3,z618,z5]),(0,[z6,z50,z274,z3,z56,z5]),(0,[z6,z2,z954,z3,z4,z5])],[(0,[z6,z23,z2,z3,z475,z5]),(0,[z6,z168,z276,z2,z3,z5]),(0,[z6,z2,z3,z12,z828,z5]),(0,[z6,z8,z2,z3,z107,z484]),(0,[z6,z412,z2,z3,z202,z5])],[(0,[z6,z8,z2,z3,z955,z4]),(0,[z6,z23,z2,z3,z576,z5]),(0,[z6,z8,z2,z3,z956,z5])],[(0,[z6,z23,z2,z3,z484,z5]),(0,[z6,z198,z2,z3,z80,z4])],[(0,[z6,z87,z23,z3,z125,z4]),(0,[z957,z8,z2,z3,z4,z5]),(0,[z68,z6,z110,z2,z3,z5])],[(0,[z958,z6,z8,z2,z4,z5]),(0,[z6,z8,z37,z2,z3,z371])]],
   [[(0,[z361,z1,z2,z3,z4,z5]),(0,[z6,z2,z3,z959,z4,z5]),(0,[z6,z493,z2,z3,z4,z5]),(0,[z6,z83,z690,z3,z4,z5]),(0,[z91,z6,z112,z8,z2,z5]),(0,[z6,z8,z50,z3,z56,z5]),(1,[z6,z8,z3,z756,z5])],[],[(0,[z6,z299,z231,z3,z4,z5]),(0,[z6,z83,z168,z2,z3,z5]),(0,[z6,z23,z2,z3,z5,z495]),(0,[z6,z2,z3,z4,z840,z5]),(0,[z68,z6,z2,z5,z221,z159])],[(0,[z6,z960,z2,z3,z4,z5]),(0,[z6,z23,z2,z3,z70,z26]),(0,[z6,z199,z2,z193,z3,z4]),(0,[z6,z198,z2,z193,z3,z4])],[(0,[z6,z23,z2,z3,z5,z500]),(0,[z6,z14,z8,z2,z3,z5]),(0,[z6,z23,z2,z3,z498,z5]),(0,[z6,z2,z3,z4,z818,z5])],[(0,[z6,z8,z2,z3,z255,z226]),(0,[z6,z2,z3,z12,z5,z158])],[(0,[z6,z961,z2,z3,z4,z5]),(0,[z6,z23,z2,z3,z12,z21]),(0,[z6,z23,z2,z3,z342,z5]),(0,[z6,z962,z2,z3,z4,z5]),(0,[z6,z87,z422,z3,z125,z4]),(0,[z68,z6,z62,z2,z3,z5]),(0,[z25,z6,z8,z2,z4,z723])],[(0,[z6,z8,z2,z3,z4,z963]),(0,[z6,z2,z3,z964,z4,z5]),(0,[z6,z8,z2,z3,z4,z777]),(0,[z6,z306,z2,z3,z4,z5]),(0,[z6,z655,z2,z3,z12,z5]),(0,[z197,z6,z168,z2,z3,z5]),(0,[z6,z198,z23,z2,z3,z70])]],
   [[(0,[z6,z8,z2,z3,z965,z5]),(0,[z6,z966,z2,z3,z4,z5]),(0,[z6,z2,z303,z231,z3,z4]),(0,[z6,z2,z3,z828,z238,z5])],[(0,[z6,z8,z2,z3,z4,z967]),(0,[z6,z117,z2,z3,z4,z5]),(0,[z11,z6,z2,z139,z135,z5]),(0,[z431,z6,z23,z2,z3,z5]),(0,[z25,z6,z92,z23,z2,z3]),(0,[z6,z8,z2,z3,z5,z882])],[(0,[z6,z352,z2,z3,z4,z5]),(0,[z6,z340,z2,z3,z4,z5]),(0,[z132,z8,z843,z3,z4,z5]),(0,[z6,z2,z3,z202,z12,z5]),(0,[z6,z968,z8,z2,z3,z4]),(0,[z6,z969,z2,z3,z4,z5])],[(0,[z6,z8,z2,z3,z4,z970]),(0,[z6,z8,z2,z3,z4,z971]),(0,[z6,z8,z37,z2,z3,z232]),(0,[z6,z972,z2,z3,z4,z5]),(0,[z973,z8,z2,z3,z4,z5])],[(0,[z6,z8,z2,z3,z974,z5]),(0,[z6,z975,z2,z3,z4,z5]),(0,[z59,z23,z2,z3,z60,z5]),(0,[z68,z6,z23,z2,z5,z159]),(0,[z6,z8,z2,z3,z13,z5])],[(0,[z6,z2,z303,z27,z3,z4]),(0,[z6,z23,z2,z3,z805,z4]),(0,[z6,z8,z2,z107,z40,z70])],[(0,[z6,z200,z2,z3,z12,z5]),(0,[z6,z8,z976,z2,z3,z4]),(0,[z144,z8,z2,z3,z4,z36]),(0,[z6,z8,z2,z3,z893,z4])],[(0,[z6,z169,z276,z2,z3,z4]),(0,[z75,z8,z2,z3,z897,z5]),(0,[z6,z2,z977,z3,z4,z5]),(0,[z11,z6,z169,z2,z135,z4]),(0,[z6,z2,z3,z778,z4,z5]),(1,[z6,z23,z2,z3,z21]),(0,[z6,z2,z3,z12,z4,z978]),(0,[z6,z2,z303,z3,z4,z21]),(0,[z91,z6,z92,z8,z2,z4])]],
   [[(0,[z6,z979,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z917]),(0,[z6,z320,z2,z321,z4,z5]),(0,[z6,z2,z3,z202,z913,z5])],[(0,[z6,z2,z3,z12,z4,z418]),(0,[z6,z2,z3,z12,z24,z5]),(0,[z6,z48,z23,z2,z3,z5]),(0,[z6,z2,z980,z3,z12,z4]),(0,[z6,z981,z2,z3,z4,z5])],[(0,[z6,z206,z2,z3,z4,z5]),(0,[z6,z982,z2,z3,z4,z5]),(0,[z6,z2,z3,z4,z5,z983]),(0,[z6,z984,z2,z3,z4,z5])],[(0,[z6,z211,z23,z2,z3,z4]),(0,[z6,z87,z3,z12,z125,z4]),(0,[z6,z2,z3,z4,z985,z5]),(0,[z6,z2,z3,z414,z4,z221])],[(0,[z6,z986,z2,z3,z4,z5]),(0,[z6,z987,z2,z3,z4,z5]),(0,[z6,z988,z2,z3,z4,z5]),(0,[z6,z23,z2,z3,z53,z4]),(0,[z6,z23,z2,z3,z5,z529]),(0,[z6,z989,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z371,z5]),(1,[z6,z8,z2,z5,z882]),(0,[z6,z990,z2,z3,z4,z5]),(0,[z6,z8,z719,z2,z3,z5])],[(1,[z8,z2,z3,z897,z5]),(0,[z35,z519,z8,z2,z3,z4]),(0,[z6,z2,z3,z12,z4,z269]),(0,[z6,z87,z163,z3,z125,z4]),(0,[z6,z288,z2,z4,z5,z40]),(0,[z6,z8,z37,z719,z2,z3])],[(0,[z6,z8,z991,z2,z3,z5]),(0,[z6,z950,z23,z2,z3,z4]),(0,[z25,z6,z412,z2,z3,z4]),(0,[z6,z992,z2,z3,z4,z5])],[(0,[z132,z8,z31,z483,z4,z5]),(0,[z6,z8,z2,z3,z4,z993]),(0,[z6,z2,z3,z908,z4,z5])]],
   [[(0,[z6,z199,z2,z3,z4,z174]),(0,[z6,z994,z2,z3,z4,z5]),(0,[z59,z433,z2,z3,z60,z5])],[(0,[z6,z23,z2,z3,z232,z5]),(0,[z6,z995,z2,z3,z4,z5])],[(0,[z59,z8,z2,z3,z897,z5]),(0,[z6,z2,z996,z3,z4,z5]),(0,[z6,z168,z8,z2,z3,z5])],[(0,[z6,z8,z2,z997,z4,z5])],[(0,[z6,z8,z2,z3,z897,z5]),(0,[z6,z92,z8,z2,z3,z173]),(0,[z6,z23,z199,z2,z3,z70]),(0,[z212,z6,z493,z103,z4,z5])],[(0,[z132,z8,z31,z3,z4,z5]),(0,[z6,z8,z2,z3,z371,z315]),(0,[z25,z6,z412,z2,z4,z26]),(0,[z6,z2,z3,z739,z371,z5])],[(0,[z6,z998,z2,z3,z4,z5]),(0,[z197,z6,z2,z4,z5,z148])],[(0,[z6,z8,z2,z3,z4,z947]),(0,[z6,z2,z3,z999,z4,z5]),(0,[z6,z8,z2,z3,z4,z948]),(0,[z6,z54,z2,z152,z4,z5]),(0,[z6,z8,z2,z3,z1000,z5]),(0,[z6,z23,z2,z3,z139,z5]),(0,[z6,z23,z42,z113,z4,z5]),(0,[z6,z2,z3,z1001,z4,z5]),(0,[z6,z2,z3,z1002,z4,z5])]],
   [[(0,[z6,z1003,z8,z3,z4,z5]),(0,[z6,z23,z168,z2,z3,z5]),(0,[z6,z8,z2,z638,z3,z107])],[(0,[z6,z2,z3,z1004,z4,z5]),(0,[z6,z527,z23,z2,z3,z5])],[(0,[z6,z123,z2,z3,z4,z15]),(0,[z6,z8,z2,z155,z4,z5]),(0,[z6,z146,z2,z155,z4,z5]),(0,[z6,z8,z2,z3,z1005,z5]),(0,[z6,z2,z3,z4,z5,z1006]),(0,[z6,z23,z2,z3,z150,z4])],[(0,[z6,z23,z2,z3,z507,z5]),(0,[z6,z1007,z2,z3,z4,z5])],[(0,[z68,z6,z23,z2,z39,z5]),(0,[z6,z8,z2,z3,z828,z5]),(0,[z6,z753,z2,z3,z371,z5]),(1,[z91,z6,z8,z2,z107])],[(0,[z6,z8,z2,z303,z3,z4]),(0,[z6,z8,z2,z3,z1008,z5])],[(0,[z6,z8,z2,z3,z4,z1009])],[(0,[z6,z8,z2,z4,z5,z1010]),(0,[z404,z8,z2,z3,z60,z5]),(0,[z6,z92,z23,z2,z3,z257]),(0,[z6,z2,z303,z3,z4,z308])]],
   [[(0,[z6,z2,z3,z4,z1011,z5]),(0,[z6,z8,z2,z3,z1012,z5]),(0,[z11,z6,z168,z2,z3,z5]),(0,[z6,z2,z3,z139,z421,z5])],[(0,[z6,z2,z3,z12,z255,z5]),(0,[z8,z2,z3,z4,z897,z5]),(0,[z6,z8,z3,z56,z756,z5]),(0,[z6,z1013,z2,z3,z4,z5])],[(0,[z6,z299,z344,z3,z4,z5]),(0,[z6,z23,z2,z3,z796,z5]),(0,[z6,z199,z2,z3,z4,z21]),(0,[z6,z2,z3,z4,z307,z21]),(0,[z6,z8,z131,z3,z4,z88])],[(0,[z6,z8,z2,z1014,z4,z5]),(0,[z6,z1015,z2,z3,z4,z5]),(0,[z6,z1016,z2,z3,z4,z5]),(0,[z102,z6,z2,z140,z4,z5]),(0,[z6,z8,z2,z38,z4,z723])],[(0,[z6,z1017,z8,z2,z3,z5]),(0,[z6,z23,z2,z3,z4,z21]),(0,[z6,z2,z3,z1018,z4,z5]),(0,[z91,z6,z2,z12,z4,z5]),(0,[z6,z1019,z2,z3,z4,z5]),(0,[z91,z6,z8,z37,z2,z5])],[(0,[z6,z1020,z8,z2,z3,z5]),(0,[z6,z1021,z2,z3,z4,z5]),(0,[z6,z199,z2,z3,z4,z307]),(0,[z6,z198,z2,z3,z4,z307]),(0,[z6,z2,z1022,z3,z4,z5]),(0,[z25,z6,z8,z2,z371,z26]),(0,[z6,z2,z3,z202,z5,z104])],[(0,[z6,z1023,z8,z2,z3,z5]),(0,[z6,z2,z3,z1024,z4,z5]),(0,[z6,z23,z2,z16,z3,z5])],[(0,[z6,z23,z2,z3,z39,z70])]],
   [[(0,[z8,z2,z3,z897,z227,z5]),(0,[z6,z8,z2,z1025,z3,z4]),(0,[z6,z1026,z2,z3,z4,z5]),(0,[z6,z938,z8,z2,z3,z4]),(0,[z91,z6,z8,z2,z4,z26])],[(0,[z6,z8,z1027,z2,z3,z4]),(0,[z6,z288,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z1028,z5]),(0,[z6,z49,z3,z115,z5,z116])],[(0,[z6,z23,z2,z3,z667,z5]),(0,[z6,z1029,z2,z3,z4,z5]),(0,[z6,z8,z2,z483,z4,z226]),(0,[z6,z169,z8,z2,z3,z139]),(0,[z6,z8,z2,z16,z434,z5]),(0,[z91,z6,z199,z8,z2,z4]),(0,[z6,z669,z8,z37,z2,z3]),(0,[z6,z2,z3,z4,z5,z1030])],[(0,[z6,z8,z2,z1031,z3,z4]),(0,[z78,z23,z2,z3,z4,z120]),(0,[z6,z2,z3,z12,z470,z5]),(0,[z6,z110,z2,z3,z4,z5])],[(0,[z6,z1032,z2,z3,z4,z5]),(0,[z6,z1033,z2,z3,z4,z5])],[(0,[z6,z2,z3,z4,z1034,z5]),(0,[z6,z83,z14,z2,z3,z5]),(0,[z41,z445,z2,z3,z4,z5]),(0,[z6,z2,z774,z3,z12,z4])],[(0,[z6,z2,z4,z307,z5,z40])],[(0,[z6,z1035,z8,z2,z3,z4]),(0,[z6,z1036,z2,z3,z4,z5]),(0,[z6,z199,z2,z3,z4,z257]),(0,[z6,z2,z303,z3,z4,z129]),(0,[z6,z8,z2,z4,z39,z456])]],
   [[(0,[z6,z2,z3,z12,z547,z5]),(0,[z6,z8,z2,z3,z4,z226]),(0,[z6,z146,z2,z3,z4,z226]),(0,[z6,z8,z1037,z3,z4,z5]),(0,[z6,z8,z3,z1038,z4,z5]),(0,[z35,z2,z3,z12,z4,z36]),(0,[z1039,z8,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z978]),(0,[z68,z25,z6,z23,z2,z5]),(0,[z437,z6,z199,z2,z3,z4])],[(0,[z1040,z6,z8,z2,z4,z5]),(0,[z6,z23,z2,z155,z4,z5]),(0,[z6,z1041,z2,z3,z4,z5])],[(0,[z6,z8,z2,z3,z1042,z5]),(0,[z75,z23,z2,z3,z227,z5]),(0,[z6,z54,z2,z321,z4,z5]),(0,[z6,z23,z2,z3,z414,z4]),(0,[z6,z2,z3,z4,z1043,z5])],[(0,[z6,z1,z2,z303,z3,z4]),(0,[z32,z8,z2,z713,z4,z5]),(0,[z6,z2,z3,z1044,z4,z5]),(0,[z6,z92,z23,z2,z3,z173]),(0,[z6,z1045,z2,z3,z4,z5])],[(0,[z6,z8,z2,z1046,z4,z5]),(0,[z6,z1047,z2,z3,z4,z5]),(0,[z6,z8,z335,z113,z4,z5]),(0,[z91,z6,z8,z2,z107,z5])],[(0,[z6,z1048,z2,z3,z4,z5]),(0,[z6,z92,z110,z2,z3,z5])],[(0,[z30,z23,z318,z3,z4,z5]),(0,[z6,z2,z3,z1049,z4,z5]),(0,[z6,z641,z2,z3,z4,z15]),(0,[z6,z8,z2,z3,z4,z1050]),(0,[z6,z8,z2,z3,z4,z269])],[(0,[z6,z213,z2,z3,z4,z5]),(0,[z6,z2,z16,z421,z17,z5])]],
   [[(0,[z30,z8,z843,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z1051]),(0,[z6,z8,z2,z778,z4,z5]),(0,[z6,z23,z2,z3,z5,z629]),(0,[z6,z23,z2,z291,z3,z5]),(0,[z6,z23,z2,z3,z307,z5])],[(0,[z6,z2,z3,z489,z4,z5]),(0,[z41,z1,z2,z3,z4,z5]),(0,[z6,z1052,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z1053,z5]),(0,[z6,z1054,z2,z3,z4,z5]),(0,[z68,z6,z8,z2,z150,z5])],[(0,[z22,z545,z2,z3,z4,z5]),(0,[z6,z1055,z2,z3,z4,z5]),(0,[z6,z8,z131,z336,z3,z4]),(0,[z6,z8,z2,z951,z3,z4]),(0,[z6,z1056,z2,z3,z4,z5]),(0,[z212,z6,z213,z103,z4,z5]),(0,[z6,z744,z2,z3,z202,z5])],[(0,[z6,z8,z2,z3,z4,z1057]),(0,[z6,z8,z2,z3,z4,z766]),(0,[z6,z2,z3,z828,z4,z5]),(0,[z6,z2,z1058,z3,z4,z5])],[(0,[z6,z8,z2,z3,z1059,z5]),(0,[z6,z8,z548,z3,z4,z88]),(0,[z6,z8,z2,z980,z3,z4]),(0,[z921,z23,z2,z3,z4,z5]),(0,[z6,z23,z317,z2,z3,z5]),(0,[z574,z2,z3,z350,z4,z5])],[(0,[z6,z1060,z2,z3,z255,z5]),(0,[z6,z2,z3,z1061,z4,z5]),(0,[z6,z299,z711,z3,z4,z5]),(0,[z6,z1062,z8,z2,z3,z5]),(0,[z6,z23,z2,z3,z421,z5]),(0,[z6,z112,z2,z3,z12,z21]),(0,[z6,z8,z2,z16,z5,z882])],[],[]],
   [[(0,[z6,z23,z2,z3,z423,z5]),(1,[z6,z711,z3,z4,z5]),(0,[z6,z83,z169,z2,z3,z4]),(0,[z6,z412,z2,z3,z4,z5]),(0,[z6,z199,z2,z287,z3,z4]),(0,[z6,z8,z37,z2,z3,z315]),(0,[z91,z6,z288,z2,z4,z5])],[(0,[z515,z276,z2,z3,z4,z5]),(0,[z6,z8,z2,z1063,z4,z5]),(0,[z197,z6,z23,z2,z3,z5]),(0,[z6,z2,z3,z4,z1064,z5]),(0,[z6,z1065,z2,z3,z4,z5])],[(0,[z6,z8,z2,z3,z255,z418])],[(0,[z6,z133,z2,z3,z203,z5]),(0,[z6,z198,z2,z3,z4,z173]),(0,[z6,z2,z250,z98,z4,z5]),(0,[z91,z6,z198,z8,z2,z4]),(0,[z6,z1066,z2,z3,z4,z5])],[(0,[z6,z276,z2,z303,z3,z4]),(0,[z6,z8,z2,z483,z255,z5]),(0,[z6,z23,z8,z2,z3,z315])],[(0,[z6,z1067,z8,z2,z3,z5]),(0,[z6,z1068,z2,z3,z4,z5]),(0,[z6,z23,z2,z3,z107,z70]),(0,[z6,z8,z2,z16,z17,z5]),(0,[z6,z110,z2,z3,z5,z70])],[(0,[z22,z276,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z1069,z4]),(0,[z6,z1070,z2,z3,z4,z5])],[(0,[z6,z8,z2,z1071,z4,z5]),(0,[z6,z23,z2,z3,z4,z226]),(0,[z6,z2,z274,z3,z4,z5]),(0,[z6,z23,z2,z3,z202,z5]),(0,[z6,z2,z1072,z3,z4,z5]),(1,[z68,z6,z8,z2,z150]),(0,[z68,z6,z8,z2,z5,z532]),(0,[z6,z8,z2,z4,z723,z26])]],
   [[(0,[z6,z8,z2,z3,z1073,z5]),(0,[z6,z23,z2,z3,z84,z5])],[(0,[z6,z8,z2,z155,z203,z5]),(0,[z6,z23,z2,z3,z203,z5]),(0,[z11,z6,z2,z401,z4,z5]),(0,[z6,z2,z3,z4,z15,z21]),(0,[z25,z6,z8,z2,z202,z26])],[(0,[z6,z8,z2,z3,z255,z5]),(0,[z6,z1074,z2,z3,z4,z5]),(0,[z6,z2,z3,z12,z4,z1075]),(0,[z6,z2,z38,z12,z4,z39])],[(0,[z6,z8,z2,z3,z1076,z5]),(0,[z8,z843,z31,z3,z4,z5]),(0,[z6,z1077,z2,z3,z4,z5]),(0,[z6,z1078,z2,z3,z4,z5]),(0,[z6,z23,z14,z2,z3,z5]),(0,[z6,z1079,z2,z3,z4,z5])],[(0,[z6,z265,z231,z3,z4,z5]),(0,[z212,z6,z103,z12,z4,z5]),(0,[z6,z198,z14,z2,z3,z15])],[(0,[z132,z31,z3,z12,z4,z5]),(0,[z6,z8,z2,z3,z1080,z5]),(0,[z25,z6,z2,z12,z4,z26]),(0,[z6,z199,z2,z3,z4,z818]),(0,[z6,z198,z2,z3,z4,z818]),(0,[z6,z8,z2,z3,z107,z315])],[(0,[z6,z1081,z2,z3,z4,z5]),(0,[z6,z2,z3,z1082,z4,z5])],[(0,[z6,z8,z2,z3,z1083,z5]),(0,[z6,z1084,z2,z3,z4,z5]),(0,[z6,z2,z3,z12,z4,z835])]],
   [[(0,[z6,z8,z2,z1085,z4,z5]),(0,[z6,z8,z2,z3,z1086,z5])],[(0,[z6,z2,z3,z139,z12,z5]),(0,[z1087,z6,z8,z2,z4,z5])],[(0,[z6,z23,z50,z3,z56,z5]),(0,[z6,z2,z3,z1088,z4,z5])],[(0,[z6,z2,z3,z4,z5,z1089]),(0,[z6,z62,z2,z3,z4,z5]),(0,[z11,z6,z14,z2,z3,z5]),(0,[z6,z23,z2,z3,z5,z315])],[(0,[z6,z2,z3,z12,z4,z5]),(0,[z1090,z6,z8,z2,z4,z5]),(0,[z1091,z8,z2,z3,z4,z5])],[(0,[z6,z8,z2,z3,z1092,z5]),(0,[z6,z69,z2,z3,z4,z5]),(0,[z212,z6,z23,z103,z4,z5]),(0,[z68,z6,z23,z2,z16,z5])],[(0,[z1,z729,z2,z3,z4,z5]),(0,[z6,z1093,z2,z3,z4,z5]),(0,[z6,z211,z760,z2,z3,z4]),(0,[z6,z23,z2,z3,z694,z5])],[(0,[z6,z2,z3,z12,z4,z724])]],
   [[(0,[z132,z146,z31,z3,z4,z5]),(0,[z6,z23,z2,z3,z411,z5]),(0,[z6,z1094,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z1095,z4])],[(0,[z6,z1096,z2,z3,z4,z5]),(0,[z35,z8,z2,z3,z4,z36]),(0,[z6,z83,z2,z303,z3,z4])],[(0,[z6,z669,z23,z2,z3,z5]),(0,[z6,z8,z2,z16,z214,z5])],[(0,[z6,z2,z1097,z3,z4,z5]),(1,[z6,z8,z747,z4,z5]),(0,[z6,z1098,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5]),(0,[z22,z729,z2,z3,z4,z5]),(0,[z6,z8,z2,z1099,z4,z5]),(0,[z6,z2,z3,z4,z5,z1100])],[(0,[z6,z1101,z2,z3,z4,z5]),(0,[z366,z545,z2,z3,z4,z5]),(0,[z6,z23,z2,z3,z840,z5]),(0,[z6,z2,z3,z12,z4,z315]),(0,[z68,z6,z8,z275,z2,z5])],[(0,[z436,z6,z8,z103,z4,z5]),(0,[z6,z23,z169,z2,z3,z4]),(0,[z6,z23,z2,z3,z13,z5]),(0,[z197,z6,z2,z303,z3,z4])],[(0,[z6,z8,z2,z3,z4,z1102]),(0,[z6,z8,z2,z3,z203,z226])]],
   [[],[(0,[z6,z8,z2,z3,z4,z1103]),(0,[z6,z8,z2,z3,z1104,z5]),(0,[z6,z8,z2,z4,z5,z40])],[(0,[z6,z211,z2,z3,z12,z4]),(0,[z6,z44,z8,z3,z5,z116]),(0,[z6,z1105,z2,z3,z4,z5]),(0,[z6,z1106,z2,z3,z4,z5]),(0,[z6,z2,z1107,z3,z4,z5])],[(0,[z6,z8,z2,z3,z1108,z5]),(0,[z6,z1109,z2,z3,z4,z5])],[(0,[z6,z1110,z2,z3,z4,z5]),(0,[z6,z1111,z2,z3,z4,z5]),(0,[z6,z1112,z2,z3,z4,z5])],[(0,[z6,z1113,z8,z2,z3,z4]),(0,[z6,z8,z2,z17,z5,z882]),(0,[z6,z1114,z2,z3,z4,z5])],[(0,[z528,z8,z2,z34,z4,z5]),(0,[z11,z6,z169,z2,z3,z4]),(0,[z6,z23,z2,z3,z371,z5]),(0,[z1115,z8,z2,z3,z4,z5]),(0,[z6,z1116,z2,z3,z4,z5])],[(0,[z6,z1117,z2,z3,z4,z5])]],
   [[(0,[z6,z23,z2,z3,z278,z5]),(0,[z6,z2,z3,z4,z115,z5]),(0,[z327,z2,z3,z207,z4,z5]),(0,[z6,z8,z2,z38,z4,z39]),(0,[z6,z1118,z2,z3,z4,z5])],[(0,[z132,z133,z31,z3,z4,z5]),(0,[z6,z1119,z2,z3,z4,z5]),(0,[z6,z169,z8,z2,z3,z4]),(0,[z1120,z8,z2,z3,z4,z5])],[(0,[z6,z8,z2,z1121,z4,z5]),(0,[z728,z8,z2,z3,z4,z5]),(0,[z6,z8,z719,z2,z3,z4])],[(0,[z6,z2,z3,z1122,z4,z5])],[(0,[z6,z8,z2,z3,z1123,z5]),(0,[z0,z2,z3,z350,z4,z5]),(0,[z75,z2,z3,z12,z227,z5]),(0,[z6,z2,z3,z4,z1124,z5]),(0,[z8,z2,z3,z4,z777,z5]),(0,[z6,z92,z23,z2,z3,z70]),(0,[z6,z8,z2,z4,z5,z882])],[(0,[z6,z623,z23,z2,z3,z5]),(0,[z6,z265,z3,z497,z4,z5]),(0,[z6,z199,z95,z2,z3,z4]),(0,[z6,z8,z2,z3,z1125,z5]),(0,[z6,z8,z113,z747,z4,z5]),(0,[z91,z6,z8,z2,z4,z5]),(0,[z6,z8,z2,z3,z1126,z5])],[(0,[z6,z133,z2,z155,z4,z5]),(0,[z6,z23,z2,z3,z357,z5]),(0,[z6,z2,z16,z12,z17,z5]),(0,[z6,z92,z37,z2,z3,z12]),(0,[z6,z1127,z2,z3,z4,z5])],[(0,[z132,z8,z31,z155,z4,z5]),(0,[z6,z8,z2,z483,z4,z418]),(0,[z132,z23,z31,z3,z4,z5]),(0,[z6,z23,z616,z2,z3,z5]),(0,[z6,z1128,z2,z3,z4,z5]),(0,[z6,z2,z250,z135,z4,z5]),(0,[z6,z2,z1129,z3,z4,z5]),(0,[z6,z23,z18,z2,z3,z5]),(0,[z6,z2,z3,z4,z5,z1130]),(0,[z6,z1131,z2,z3,z4,z5])]],
   [[(1,[z729,z2,z3,z4,z5]),(0,[z6,z1060,z2,z3,z4,z5]),(0,[z6,z8,z2,z1132,z4,z5]),(0,[z6,z1133,z2,z3,z4,z5])],[(0,[z6,z416,z2,z3,z4,z5]),(0,[z6,z23,z2,z3,z249,z5]),(0,[z6,z2,z3,z4,z5,z104]),(0,[z6,z23,z2,z3,z99,z5]),(1,[z6,z8,z719,z2,z3])],[(0,[z132,z8,z194,z31,z3,z4]),(0,[z6,z1134,z2,z3,z4,z5]),(0,[z30,z318,z3,z12,z4,z5]),(0,[z6,z2,z3,z4,z5,z1135]),(0,[z6,z8,z2,z3,z584,z70]),(0,[z6,z14,z2,z3,z12,z5]),(0,[z6,z1136,z2,z3,z4,z5]),(0,[z68,z6,z8,z2,z484,z5])],[(0,[z6,z8,z2,z3,z4,z1075]),(0,[z6,z83,z376,z3,z4,z5]),(0,[z6,z8,z2,z3,z53,z139]),(0,[z68,z6,z8,z37,z2,z39])],[(0,[z6,z2,z3,z1137,z4,z5]),(0,[z6,z8,z219,z3,z56,z5]),(0,[z6,z2,z3,z4,z5,z221]),(0,[z6,z2,z3,z4,z15,z818])],[(0,[z6,z8,z2,z3,z4,z418]),(0,[z6,z146,z2,z3,z4,z418]),(0,[z6,z211,z1077,z2,z3,z4]),(0,[z6,z1138,z2,z3,z4,z5]),(0,[z6,z2,z27,z4,z5,z516]),(0,[z6,z199,z8,z2,z3,z13]),(0,[z6,z198,z8,z2,z3,z13]),(0,[z6,z208,z8,z2,z3,z70])],[(0,[z327,z276,z2,z3,z4,z5]),(0,[z6,z8,z2,z3,z4,z1139]),(0,[z6,z23,z2,z3,z828,z5]),(0,[z6,z42,z113,z12,z4,z5]),(0,[z1140,z8,z2,z3,z4,z5]),(0,[z6,z2,z3,z1141,z4,z5]),(0,[z91,z6,z8,z2,z4,z315])],[(0,[z6,z729,z2,z3,z4,z5]),(0,[z6,z8,z2,z483,z4,z5]),(0,[z6,z23,z2,z303,z3,z4]),(0,[z6,z23,z2,z3,z480,z5]),(0,[z6,z23,z2,z3,z121,z5]),(0,[z6,z112,z2,z3,z307,z5]),(0,[z6,z1142,z2,z3,z4,z5]),(0,[z6,z2,z3,z4,z1143,z5]),(0,[z6,z412,z2,z38,z3,z4])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 527) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 527).take 530) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1057).take 136) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1193)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [527, 530, 136] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 99).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 99).take 108).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 207).take 49).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [99, 108, 49] = true :=
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

end PEqualNP.Outside.L_meta_41698

theorem PEqualNP.Outside.L_meta_41698 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676840 * 2 ^ 32 + 3938511040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676840 * 2 ^ 32 + 3938511040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_41698.solve