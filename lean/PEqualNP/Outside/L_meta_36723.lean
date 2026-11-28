import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_36723

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
  Nat.testBit (4008372968 * 2 ^ 32 + 4008372896) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0xa481400010090049#64 ++ 0x09c002085800a0aa#64 ++ 0xffc7c0fc7e3ff1ff#64 ++ 0xfff44f3c7d11f1ff#64 : BitVec 256),
   (0x61488b0c86423210#64 ++ 0x79e3249314cccccc#64 ++ 0xe3f8ff1f8fc77e3b#64 ++ 0xffebb4d39eeececc#64 : BitVec 256),
   (0x025215600a905482#64 ++ 0x820c1862a30b0b05#64 ++ 0x03ff3fe00ff87fc3#64 ++ 0xbafc38e3e30f0f0f#64 : BitVec 256),
   (0x480026b520006920#64 ++ 0xd20ec0f403b00750#64 ++ 0xfc003ffff0007ffc#64 ++ 0xd34fc0fc03f00ff0#64 : BitVec 256),
   (0x000038da4d240000#64 ++ 0xa20dfd0003775000#64 ++ 0x00003fffffff8000#64 ++ 0xe38fff0003fff000#64 : BitVec 256),
   (0x93a4000000000000#64 ++ 0xf40ffffdec000000#64 ++ 0xffffc00000000000#64 ++ 0xfc0ffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [8, 7]⟩, ⟨.and, [7, 4]⟩, ⟨.or, [2, 10]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [0, 12]⟩, ⟨.or, [9, 4]⟩, ⟨.and, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x000038da4d240000 0xa20dfd0003775000 0x00003fffffff8000 0xe38fff0003fff000

def z1 : W := mkw 0x025215600a905482 0x820c1862a30b0b05 0x03ff3fe00ff87fc3 0xbafc38e3e30f0f0f

def z2 : W := mkw 0x480026b520006920 0xd20ec0f403b00750 0xfc003ffff0007ffc 0xd34fc0fc03f00ff0

def z3 : W := mkw 0x61488b0c86423210 0x79e3249314cccccc 0xe3f8ff1f8fc77e3b 0xffebb4d39eeececc

def z4 : W := mkw 0x93a4000000000000 0xd40ec2fdec000000 0xffffc00000000000 0xdc0fc0fffc000000

def z5 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0xffffc00000000000 0xfc0ffffffc000000

def z6 : W := mkw 0xa481400010090049 0x09c002085800a0aa 0xffc7c0fc7e3ff1ff 0xfff44f3c7d11f1ff

def z7 : W := mkw 0x93a438da4d240000 0xf60ffffdef775000 0xffffffffffff8000 0xff8ffffffffff000

def z8 : W := mkw 0xa481400010090049 0x09c002085800a0aa 0xffc7c000000071ff 0x1c70003c7c0001ff

def z9 : W := mkw 0x8481400010090049 0x0000020848002022 0x1fc700e07e38f1c7 0xbaf44b2c6111313f

def z10 : W := mkw 0x0200000000000000 0x800c1860a0000000 0x03ff000000000000 0xb80c38e3e0000000

def z11 : W := mkw 0x93f615600a905482 0xf60fffffef0b0b05 0xffffffe00ff87fc3 0xfeffffffff0f0f0f

def z12 : W := mkw 0x92a4000000000000 0x840cdb6ce8000000 0x1c07000000000000 0x00044b2c60000000

def z13 : W := mkw 0xf3ec8b0c86423210 0xfdeffffffccccccc 0xffffff1f8fc77e3b 0xffeffffffeeececc

def z14 : W := mkw 0x0000080804000000 0x2001240000444000 0x00003fffffff8000 0xe38fff0003fff000

def z15 : W := mkw 0x000038da4d240000 0xa20dfd0003775000 0x00003f1f8fc70000 0xe38bb40002eec000

def z16 : W := mkw 0x265355601a9954cb 0x8bcc1862b30babaf 0x03ff3ffc7fffffff 0xbbfc38e3e31fffff

def z17 : W := mkw 0x480026b520006920 0x820cc00003b00750 0x00003ffff0007ffc 0xc34fc00003f00ff0

def z18 : W := mkw 0x93a4000000000000 0x540202fdec000000 0xffffc00000000000 0x1c0000fffc000000

def z19 : W := mkw 0x93a438da4d240000 0xf60ffffdef775000 0xffffff0381c00000 0xfc0ffffffeee0000

def z20 : W := mkw 0x4800229520002920 0x5002c09400b00450 0xfc00001ff000003c 0x4103c01c00f000f0

def z21 : W := mkw 0xdba4229520002920 0xf40ffffdecb00450 0xffffc01ff000003c 0xfd0ffffffcf000f0

def z22 : W := mkw 0x93a4000000000000 0x24013f09ec000000 0x03ffc00000000000 0x2c003f03fc000000

def z23 : W := mkw 0x0040010002001000 0x0000000200080804 0x03f83f000fc07e03 0xbae830c3820e0e0c

def z24 : W := mkw 0x0100000000000000 0x7003249104000000 0xe3f8c00000000000 0xfc0bb4d39c000000

def z25 : W := mkw 0x480026b520006920 0xd20ec0f403b00750 0xffc73ffffe387fff 0xfbffc8fc63f10fff

def z26 : W := mkw 0xe5c9cb0c964b3259 0x79e3269b5cccecee 0xffffffffffffffff 0xffffffffffffffff

def z27 : W := mkw 0x025215600a905482 0x820c1862a30b0b05 0x03ff3f0001c00e00 0xb80c38e3e20e0e00

def z28 : W := mkw 0x69488f2da6427b30 0x79e324f714cccfdc 0xfff8ff1f8fc77fff 0xffebb4ff9eeecffc

def z29 : W := mkw 0x91a4000000000000 0x7403e79d4c000000 0xfff8c00000000000 0xfc0bf7df9c000000

def z30 : W := mkw 0x8280000000000000 0x800c1a68e8000000 0xffffc00000000000 0xfc0c7ffffc000000

def z31 : W := mkw 0xa6d355601a9954cb 0x8bcc1a6afb0babaf 0xfffffffc7fffffff 0xfffc7fffff1fffff

def z32 : W := mkw 0x2401400010090049 0x09c000001000a0aa 0xfc0000fc7e3ff1ff 0xd3f4403c0111f1ff

def z33 : W := mkw 0x025215600a905482 0x820c1862a30b0b05 0x00073fe00ff87fc3 0x02f40820630f0f0f

def z34 : W := mkw 0x41488b0c86423210 0x7023249304cc4c44 0x00383f0381c00e00 0x000bb0c382ee0e00

def z35 : W := mkw 0x0000209000000000 0x0200000003300000 0x00003ffff0000000 0x0300000003f00000

def z36 : W := mkw 0x6148830482423210 0x59e2009314888ccc 0xe3f8c00000007e3b 0x1c6000d39c000ecc

def z37 : W := mkw 0xdba426b520006920 0xf60ffffdefb00750 0xfffffffff0007ffc 0xff4ffffffff00ff0

def z38 : W := mkw 0x5b2426b520006920 0xf60ffdf5a7b00750 0x00383f0380000e00 0x000bb0c382e00e00

def z39 : W := mkw 0x4148bbdecf663210 0xf22ffd9307ff5c44 0x00383fffffff8e00 0xe38fffc383fffe00

def z40 : W := mkw 0xa6d37dfa5fbd54cb 0xabcdff6afb7ffbaf 0xffffffffffffffff 0xffffffffffffffff

def z41 : W := mkw 0x0000000000000000 0x800cd90000000000 0x0000000000000000 0x00044b0000000000

def z42 : W := mkw 0x480026b520006920 0x520200f403b00750 0xfc003ffff0007ffc 0x134000fc03f00ff0

def z43 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0x03ffc00000000000 0x2c0bbfc3fc000000

def z44 : W := mkw 0x2000000000000000 0x09c0000010008088 0xe3c0c01c0e07703b 0xffe004101c00c0cc

def z45 : W := mkw 0x6948ab9da6423b30 0x79e3e49714fcccdc 0xfff8ff1fffc77e3f 0xffebf4df9efecefc

def z46 : W := mkw 0x0000000000000000 0x0000000000000000 0x03f8000000000000 0xb80830c380000000

def z47 : W := mkw 0x0000000000000000 0x800cc06400000000 0x1c00000000000000 0x0004402c00000000

def z48 : W := mkw 0x2148890886421210 0x29e12403144cc88c 0x03f8c0000fc70003 0x2ca034039c0ec00c

def z49 : W := mkw 0x0000000000000000 0x2001240000000000 0x0000000000000000 0xe00bb40000000000

def z50 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z51 : W := mkw 0x60488b0c86423210 0x09e0000210cccccc 0x00003f1f8fc77e3b 0x03e0000002eececc

def z52 : W := mkw 0x92a4000000000000 0x840cdb6ce8000000 0xffc7c00000000000 0xfc044f3c7c000000

def z53 : W := mkw 0x005215600a905482 0x02000002030b0b05 0x00003fe00ff87fc3 0x02f00000030f0f0f

def z54 : W := mkw 0x9ba424b120004920 0xf60ffffdef300310 0xffffc0e0700001c4 0xfc0ffffffd100130

def z55 : W := mkw 0x4100020400002000 0x7003249104800440 0xe3f8ff1f80007e38 0xff4bb4d39ee00ec0

def z56 : W := mkw 0x0000000000000000 0x0000000000000000 0xfc0000fc700071fc 0xd344403c011001f0

def z57 : W := mkw 0x61488b0c86423210 0x79e3249314cccccc 0x03f8ff038fc70e03 0x2cabb4c39eeece0c

def z58 : W := mkw 0x61488f2c86427210 0xfbef24f317cccfcc 0xe3f8ffff8fc77ffb 0xffefb4f39feecfcc

def z59 : W := mkw 0x0000000000000000 0xd00ec0f400000000 0xfc00000000000000 0xd00fc0fc00000000

def z60 : W := mkw 0x60088a0c84422210 0x09e0000010c4c4c8 0x0000001f80070038 0x0100000000e0c0c0

def z61 : W := mkw 0x1324000000000000 0xf40ffdf5a4000000 0xe3f8c00000000000 0xfc0bb4d39c000000

def z62 : W := mkw 0x0000000000000000 0xa00dfd0000000000 0x000000fc7e3f8000 0xe38fff000111f000

def z63 : W := mkw 0xa481400010090049 0x09c002085800a0aa 0xffc7c0e00e3871ff 0xbef4083c7d0101ff

def z64 : W := mkw 0x000038da4d240000 0xa20dfd0003775000 0xfc003ffffffff1fc 0xf3cfff3c03fff1f0

def z65 : W := mkw 0x0040010002001000 0x0000000200080804 0x00003f000fc07e03 0x02e00000020e0e0c

def z66 : W := mkw 0x6848afbda6427b30 0xdbeec0f613fccfdc 0xfc003fffffc77fff 0xd3efc0fc03fecffc

def z67 : W := mkw 0xdbf637f52a907da2 0xf60fffffefbb0f55 0xfffffffffff87fff 0xffffffffffff0fff

def z68 : W := mkw 0xa481400010090049 0x09c002085800a0aa 0x03c7c0000e3f8003 0x2cb00f007c01f00f

def z69 : W := mkw 0x6148ab9c86423210 0xfbefe49317fccccc 0xe3f8ffffffc77e3b 0xffeff4d39ffececc

def z70 : W := mkw 0x0000000000000000 0x0000000000000000 0x03c700e00e3871c3 0xbaf408206101010f

def z71 : W := mkw 0x480026b520006920 0xd20ec0f403b00750 0x00003f0380000e00 0x000b80c002e00e00

def z72 : W := mkw 0x0040090806001000 0x20012402004c4804 0x03f83f1f8fc77e03 0xfbebb4c382eece0c

def z73 : W := mkw 0x485237f52a907da2 0xd20ec0f603bb0f55 0xfc003ffffff87fff 0xd3ffc0fc03ff0fff

def z74 : W := mkw 0xa6d34520129954cb 0x09c0026af808abaf 0xffffc00000007fff 0x1c7000fffc000fff

def z75 : W := mkw 0xa48178da5d2d0049 0xabcdff085b77f0aa 0xffc7fffffffff1ff 0xffffff3c7ffff1ff

def z76 : W := mkw 0x000038da4d240000 0xa20dfd0003775000 0x00003f0381c00000 0x000bb00002ee0000

def z77 : W := mkw 0x92a4000000000000 0x840cdb6ce8000000 0x1fff000000000000 0xb80c7befe0000000

def z78 : W := mkw 0xa6d355601a9954cb 0x8bcc1a6afb0babaf 0x03ffffe00fffffc3 0xbefc3fe3ff0fff0f

def z79 : W := mkw 0x8080000000000000 0x0000020848000000 0xffc7c00000000000 0xfc044f3c7c000000

def z80 : W := mkw 0xb7a5400010090049 0xfdcffffdfc00a0aa 0xffffc0fc7e3ff1ff 0xfffffffffd11f1ff

def z81 : W := mkw 0x000030d249240000 0x820cd90003331000 0x000000e070388000 0x00044b0001113000

def z82 : W := mkw 0x93f611400a901482 0xf40fffffec0b0805 0xffffc0000ff80003 0xfcbffffffc0f000f

def z83 : W := mkw 0x480026b520006920 0x5202c09403b00750 0xfc003ffff0007ffc 0x4343c01c03f00ff0

def z84 : W := mkw 0x000038da4d240000 0x0200000003775000 0x00003fffffff8000 0x0380000003fff000

def z85 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000fc7e3f8000 0xe3844f000111f000

def z86 : W := mkw 0x480026b520006920 0xd20ec0f403b00750 0xfc003f0380007ffc 0x104b80fc02e00ff0

def z87 : W := mkw 0x0000209000000000 0x820cc00003300000 0x00003ffffe3f8000 0xe38fcf0003f1f000

def z88 : W := mkw 0x0100000000000000 0x2001240104000000 0x03f8c00000000000 0x2c0034039c000000

def z89 : W := mkw 0x0252194a4fb41482 0x20013d02a04f5805 0x03ff00000fff8003 0x28b03f03e00ff00f

def z90 : W := mkw 0x0000080804000000 0x2001240000444000 0x00003f1f8fc70000 0xe38bb40002eec000

def z91 : W := mkw 0x0000184a4d240000 0x20013d0000475000 0x000000000fff8000 0x20803f00000ff000

def z92 : W := mkw 0xe5c9fbdedf6f3259 0xfbefff9b5ffffcee 0xffffffffffffffff 0xffffffffffffffff

def z93 : W := mkw 0x93a4000000000000 0x740326fdec000000 0xffffc00000000000 0xfc0bb4fffc000000

def z94 : W := mkw 0x48003eff6d246920 0xf20ffdf403f75750 0xfc003ffff1c07ffc 0xd34ff0fc03fe0ff0

def z95 : W := mkw 0x4800062520006920 0x500200f400800750 0xfc0000fc70007ffc 0xd34440fc01100ff0

def z96 : W := mkw 0x025211400a901482 0x00001802a00b0805 0x03ff00000ff80003 0x28b03803e00f000f

def z97 : W := mkw 0xa481400010090049 0x09c002085800a0aa 0xfc00c01c7007803c 0x4500471c1c10f0f0

def z98 : W := mkw 0x8080000000000000 0x0000020848000000 0xffc7c0fc700071fc 0xff444f3c7d1001f0

def z99 : W := mkw 0x8481400010090049 0x0000020848002022 0x1c0700e0703881c4 0x00144b2c61113133

def z100 : W := mkw 0xe589ca0c944b2259 0x79e326995cc4e4ea 0xfc00c01ff007803c 0x4503c71c1cf0f0f0

def z101 : W := mkw 0x41488b0c86423210 0x7023249304cc4c44 0xe3f8ff0381c00e00 0xfc0bb4d39eee0e00

def z102 : W := mkw 0x02523dfa4fb45482 0xa20dfd62a37f5b05 0x03ff3fffffffffc3 0xfbffffe3e3ffff0f

def z103 : W := mkw 0x0000000000000000 0x0000000000000000 0x03c70000000071c3 0x187000206000010f

def z104 : W := mkw 0x61488b0c86423210 0x79e3249314cccccc 0xe3f8ff0381c07e3b 0x1c6bb0d39eee0ecc

def z105 : W := mkw 0x41088a0c84422210 0x7023249104c44440 0x0000000380000000 0x0003800000e00000

def z106 : W := mkw 0xd9a426b520006920 0xf60fe7fd4fb00750 0xfc00fffff0007ffc 0xd74fc7fc1ff00ff0

def z107 : W := mkw 0x480026b520006920 0xd20ec0f403b00750 0xfc003ffffe3ffffc 0xf3cfcffc03f1fff0

def z108 : W := mkw 0x4a5237f52a907da2 0xd20ed8f6a3bb0f55 0x00383f0381c00e00 0x000bb0c382ee0e00

def z109 : W := mkw 0x0000209000000000 0x820cc00003300000 0x00003ffff0000000 0xc30fc00003f00000

def z110 : W := mkw 0x0100000000000000 0x7003249104000000 0xe000c00000000000 0x440384101c000000

def z111 : W := mkw 0xe5c9c304924b3259 0x59e2029b5c88acee 0xffffc00000007fff 0x1c7000fffc000fff

def z112 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000001c70078000 0x410047000010f000

def z113 : W := mkw 0xdba426b520006920 0xd60ec2fdefb00750 0xfffffffff0007ffc 0xdf4fc0fffff00ff0

def z114 : W := mkw 0x93a4000000000000 0xa40d3f69ec000000 0x03ffc00000000000 0xbc0c3fe3fc000000

def z115 : W := mkw 0xa481400010090049 0x09c002085800a0aa 0x1fc7c0e07e3f81c7 0x2cb44f2c7d11f13f

def z116 : W := mkw 0x2401400010090049 0x09c000001000a0aa 0x000000fc7e3ff1ff 0x03f000000111f1ff

def z117 : W := mkw 0xec8166b530096969 0xdbcec2fc5bb0a7fa 0xffc7fffffe3fffff 0xffffcffc7ff1ffff

def z118 : W := mkw 0x480026b520006920 0xd20ec0f403b00750 0xfc003f0380000e00 0xd00fc0fc02e00e00

def z119 : W := mkw 0x0000000000000000 0x0000000000000000 0x00003f1f80000000 0xc30b800002e00000

def z120 : W := mkw 0xec817eff7d2d6969 0xfbcffffc5bf7f7fa 0xffc7ffffffffffff 0xfffffffc7fffffff

def z121 : W := mkw 0x0000042000004000 0x820c006003000300 0x00003fe000007fc0 0x924c00e003000f00

def z122 : W := mkw 0x61088a0c84422210 0x79e3249114c4c4c8 0xe000c01f80070038 0x450384101ce0c0c0

def z123 : W := mkw 0x1324000000000000 0xf40ffdf5a4000000 0x03ff000000000000 0xb80fb8e3e0000000

def z124 : W := mkw 0x080024b120004920 0x820cc06403300310 0x1c0000e0700001c4 0x0004402c01100130

def z125 : W := mkw 0x010038da4d240000 0xf20ffd9107775000 0xe3f8ffffffff8000 0xff8fffd39ffff000

def z126 : W := mkw 0x1224000000000000 0x840cd964a0000000 0x0000000000000000 0x0000000000000000

def z127 : W := mkw 0x0000104008000000 0x820c180003030000 0x00003fe00ff80000 0xa28c3800030f0000

def z128 : W := mkw 0x93a4104008000000 0xf60ffffdef030000 0xffffffe00ff80000 0xfe8fffffff0f0000

def z129 : W := mkw 0x93a4209000000000 0xf60ffffdef300000 0xfffffffff0000000 0xff0ffffffff00000

def z130 : W := mkw 0x4000020400002000 0x5002009000800440 0xe0003f1f80007e38 0xd34b80d002e00ec0

def z131 : W := mkw 0x4800062520006920 0x500200f400800750 0xfc00000000007ffc 0x104000fc00000ff0

def z132 : W := mkw 0x61488b0c86423210 0x79e3249314cccccc 0xe3f8c01f8fc7003b 0x6da3b4139ceec0cc

def z133 : W := mkw 0x4a0026b520006920 0xd20ed8f4a3b00750 0xffff3ffff0007ffc 0xfb4ff8ffe3f00ff0

def z134 : W := mkw 0x0000289804000000 0xa20de40003744000 0x00003fffffc70000 0xe38ff40003fec000

def z135 : W := mkw 0x40488b0c86423210 0x0020000200cc4c44 0x00003f0381c00e00 0x0000000002ee0e00

def z136 : W := mkw 0x1324000000000000 0xf40ffdf5a4000000 0x0038000000000000 0x000bb0c380000000

def z137 : W := mkw 0x0000289a45240000 0x2001e50000745000 0x0000001ff0078000 0x4103c70000f0f000

def z138 : W := mkw 0x93a4000000000000 0x7403ff9dec000000 0xffffc00000000000 0x6c03ff1ffc000000

def z139 : W := mkw 0x2148890886421210 0x29e12403144cc88c 0x03f8ff000fc77e03 0xbee834c39e0ece0c

def z140 : W := mkw 0x93a438da4d240000 0xa60dff09ef775000 0x03ffffffffff8000 0xef8fff03fffff000

def z141 : W := mkw 0x4a5237f52a907da2 0xd20ed8f6a3bb0f55 0xffff3ffffff87fff 0xfbfff8ffe3ff0fff

def z142 : W := mkw 0x0000184a4d240000 0x0000000000475000 0x000000000fff8000 0x00800000000ff000

def z143 : W := mkw 0xdba426b520006920 0xf60ffffdefb00750 0xffffff0380000e00 0xfc0ffffffee00e00

def z144 : W := mkw 0x0000080804000000 0x2001240000444000 0x0000001f80070000 0x4103840000e0c000

def z145 : W := mkw 0x080034f369244920 0x820cd96403331310 0x1c0000e0703881c4 0x00044b2c01113130

def z146 : W := mkw 0xe5c9cb0c964b3259 0x79e3269b5cccecee 0xffffff1f8fc77fff 0xfffbb4fffeeecfff

def z147 : W := mkw 0x00003cfa4d244000 0xa20dfd6003775300 0x00003fffffffffc0 0xf3cfffe003ffff00

def z148 : W := mkw 0x0212146008904482 0x820c1860a3030301 0x000700e0003801c0 0x0014082061010103

def z149 : W := mkw 0x4a1236f528906da2 0xd20ed8f4a3b30751 0xfc073ffff0387ffc 0xd35fc8fc63f10ff3

def z150 : W := mkw 0xe589ca0c944b2259 0x79e326995cc4e4ea 0xffc7c0fffe3ff1ff 0xfff7cf3c7df1f1ff

def z151 : W := mkw 0x480026b520006920 0x0200000003b00750 0x00003ffff0007ffc 0x0340000003f00ff0

def z152 : W := mkw 0x93a4000000000000 0x24013f09ec000000 0xffffc00000000000 0xfc047f3ffc000000

def z153 : W := mkw 0x48003eff6d246920 0xf20ffdf403f75750 0xfc003ffffffffffc 0xf3cffffc03fffff0

def z154 : W := mkw 0x245355601a9954cb 0x0bc00002130babaf 0x00003ffc7fffffff 0x03f00000031fffff

def z155 : W := mkw 0x4000020400002000 0x5002009000800440 0xfc003ffff0007ffc 0xd34fc0fc03f00ff0

def z156 : W := mkw 0x025215600a905482 0x00001862a00b0b05 0x03ff00000ff87fc3 0x38f038e3e00f0f0f

def z157 : W := mkw 0x025211400a901482 0x820c1802a30b0805 0x03ff3fe00ff80003 0xaabc3803e30f000f

def z158 : W := mkw 0x0000000000000000 0x500200f400000000 0xfc00000000000000 0x100000fc00000000

def z159 : W := mkw 0x635a97648ad27692 0xdbee18f3b78b8fcd 0xe3ffffe00ff87ffb 0xbefc38f3ff0f0fcf

def z160 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0xffffc0e00e3871c3 0xfefffffffd01010f

def z161 : W := mkw 0x6948afbda6427b30 0xfbefe4f717fccfdc 0xfff8ffffffc77fff 0xffeff4ff9ffecffc

def z162 : W := mkw 0x0000000000000000 0x0000000000000000 0xfc00000000000000 0xd004403c00000000

def z163 : W := mkw 0xa481400010090049 0x09c002085800a0aa 0xfc00c0fc7e3f803c 0xe7844f1c1d11f0f0

def z164 : W := mkw 0x0000000000000000 0x0000000000000000 0x03c000000e007003 0xbae000000000000c

def z165 : W := mkw 0x635a9f6c8ed27692 0xfbef3cf3b7cfcfcd 0xe3ffffff8fff7ffb 0xffffbcf3ffefcfcf

def z166 : W := mkw 0x025215600a905482 0x820c1862a30b0b05 0x03ff3f000ff80e03 0x28b838c3e20f0e0f

def z167 : W := mkw 0x2148890886421210 0x29e12403144cc88c 0xe3f8c01c0fc7703b 0xffe034139c0ec0cc

def z168 : W := mkw 0x61489b4ecf663210 0x79e33d9314cfdccc 0xe3f8ff1f8ffffe3b 0xffebbfd39eeffecc

def z169 : W := mkw 0x000030d249240000 0x0200000003331000 0x000000e070388000 0x0000000001113000

def z170 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0xe0044f0000000000

def z171 : W := mkw 0x1324000000000000 0x540200f5a4000000 0x0038000000000000 0x000000c380000000

def z172 : W := mkw 0x93a4000000000000 0x540202fdec000000 0xffffc00000000000 0xfc044ffffc000000

def z173 : W := mkw 0x0012146008904482 0x0200000003030301 0x000000e0003801c0 0x0010000001010103

def z174 : W := mkw 0x91a4000000000000 0x7403e79d4c000000 0xfc00c00000000000 0x4403c71c1c000000

def z175 : W := mkw 0x000030d249240000 0x820cd90003331000 0x00003ffff0388000 0xc30fcb0003f13000

def z176 : W := mkw 0x93a4000000000000 0xd40e1afdec000000 0xffffc00000000000 0xbc0c38fffc000000

def z177 : W := mkw 0x6148bbdecf663210 0xfbeffd9317ffdccc 0xe3f8fffffffffe3b 0xffefffd39ffffecc

def z178 : W := mkw 0xa48178da5d2d0049 0xabcdff085b77f0aa 0x03c7ffffffff8003 0xefbfff007ffff00f

def z179 : W := mkw 0x0252010002901482 0x00000002a0080805 0x03ff000000000003 0x08300003e000000f

def z180 : W := mkw 0x0100000000000000 0xf00ffd9104000000 0xe3f8c00000000000 0xfc0fffd39c000000

def z181 : W := mkw 0x0000000000000000 0xa00dfd0000000000 0x0000000000000000 0xe00fff0000000000

def z182 : W := mkw 0x41488b0c86423210 0x7023249304cc4c44 0x00383f1f8fc70e00 0xe38bb4c382eece00

def z183 : W := mkw 0x91a4000000000000 0x240127094c000000 0x0000c00000000000 0x040007001c000000

def z184 : W := mkw 0xa481400010090049 0x09c002085800a0aa 0xfc00c0fc7e3ff1ff 0x47f0471c1d11f1ff

def z185 : W := mkw 0x000038da4d240000 0xa20dfd0003775000 0x00003f038fff8000 0x208bbf0002eff000

def z186 : W := mkw 0x0000000000000000 0x0000000000000000 0xe3c0c00000000000 0xfc0004101c000000

def z187 : W := mkw 0x93f6052002905482 0xf40fffffec080b05 0xffffc00000007fc3 0xfc7ffffffc000f0f

def z188 : W := mkw 0x0000209000000000 0xd20ec0f403300000 0xfc003ffff0000000 0xd30fc0fc03f00000

def z189 : W := mkw 0x2401400010090049 0x09c000001000a0aa 0x00000000000071ff 0x00700000000001ff

def z190 : W := mkw 0x93f615600a905482 0xd60e1affef0b0b05 0xffffffe00ff87fc3 0xbefc38ffff0f0f0f

def z191 : W := mkw 0x0252052002905482 0x800c1862a0080b05 0x03ff000000007fc3 0xb87c38e3e0000f0f

def z192 : W := mkw 0x0000104008000000 0x0000180000030000 0x000000000ff80000 0x20803800000f0000

def z193 : W := mkw 0x025215600a905482 0x820c1862a30b0b05 0x00383fe00ff80e00 0xa28c38c3830f0e00

def z194 : W := mkw 0x0000000000000000 0x0000000000000000 0x03c700000e380003 0x28b008006001000f

def z195 : W := mkw 0x4800229520002920 0x5002c09400b00450 0xfc003f1ff0007e3c 0xd34bc0dc02f00ef0

def z196 : W := mkw 0x93f6052002905482 0x540202ffec080b05 0xffffc00000007fc3 0x1c7000fffc000f0f

def z197 : W := mkw 0xe481420410092049 0x59c202985880a4ea 0xffc7fffffe3fffff 0xffffcffc7ff1ffff

def z198 : W := mkw 0x000038da4d240000 0xa20dfd0003775000 0x00003ffff1c00000 0xc30ff00003fe0000

def z199 : W := mkw 0x6048bbdecf663210 0xabedfd0213ffdccc 0x00003ffffffffe3b 0xe3efff0003fffecc

def z200 : W := mkw 0xcc8166b530096969 0xd20ec2fc4bb02772 0xfc073ffff038fffc 0xd35fcbfc63f13ff3

def z201 : W := mkw 0x4800229520002920 0x0000000000b00450 0x0000001ff000003c 0x0100000000f000f0

def z202 : W := mkw 0x0a5235f12a905da2 0x820cd866a33b0b15 0x1fff3fe07ff87fc7 0xbafc78efe31f0f3f

def z203 : W := mkw 0x4a5237f52a907da2 0xd20ed8f6a3bb0f55 0x03ff3fe38ff87fc3 0xbaffb8e3e3ef0f0f

def z204 : W := mkw 0x680026b520006920 0xdbcec0f413b087d8 0xffc0fffffe077fff 0xffefc4fc1ff0cffc

def z205 : W := mkw 0x93a4000000000000 0xa40dff09ec000000 0x03ffc00000000000 0xec0fff03fc000000

def z206 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0xfc07c00000000000 0x4407cf3c7c000000

def z207 : W := mkw 0x93a4289a45240000 0xf40ffffdec745000 0xffffc01ff0078000 0xfd0ffffffcf0f000

def z208 : W := mkw 0x93a4000000000000 0x04000209ec000000 0x03ffc00000000000 0x0c000003fc000000

def z209 : W := mkw 0x0a1234f128904da2 0x820cd864a3330311 0x1c0700e0703801c4 0x0014482c61110133

def z210 : W := mkw 0x485237f52a907da2 0x0200000203bb0f55 0x00003ffffff87fff 0x03f0000003ff0fff

def z211 : W := mkw 0x0200000000000000 0x800c1860a0000000 0x0007000000000000 0x0004082060000000

def z212 : W := mkw 0x93b6146008904482 0xf60ffffdef030301 0xffffc0e0003801c0 0xfc1ffffffd010103

def z213 : W := mkw 0x02523dfa4fb45482 0xa20dfd62a37f5b05 0x00383fffffff8e00 0xe38fffc383fffe00

def z214 : W := mkw 0x8180000000000000 0x700326994c000000 0xffffc00000000000 0xfc0ffffffc000000

def z215 : W := mkw 0x0000080804000000 0x0000000000444000 0x00003f1f8fc70000 0x0380000002eec000

def z216 : W := mkw 0x0252052002905482 0x00000062a0080b05 0x03ff000000007fc3 0x187000e3e0000f0f

def z217 : W := mkw 0xdba4062520006920 0xf40ffffdec800750 0xffffc00000007ffc 0xfc4ffffffc000ff0

def z218 : W := mkw 0xedc9efbdb64b7b79 0xfbefe6ff5ffceffe 0xffffffffffffffff 0xffffffffffffffff

def z219 : W := mkw 0xe4c9cb0c964b3259 0x09e0020a58ccecee 0xffc7ffffffffffff 0xfff44f3c7fffffff

def z220 : W := mkw 0xb7a5400010090049 0xfdcffffdfc00a0aa 0xffffc01c7007803c 0xfd0ffffffc10f0f0

def z221 : W := mkw 0xfbecafbda6427b30 0xffeffffffffccfdc 0xffffffffffc77fff 0xffeffffffffecffc

def z222 : W := mkw 0x480026b520006920 0x5002c0f400b00750 0xfc00001ff0007ffc 0x5143c0fc00f00ff0

def z223 : W := mkw 0xb7a578da5d2d0049 0xffcffffdff77f0aa 0xfffffffffffff1ff 0xfffffffffffff1ff

def z224 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0x1c3f000000000000 0x000ffbefe0000000

def z225 : W := mkw 0x1124000000000000 0x7403e59504000000 0x0000000000000000 0x0003800000000000

def z226 : W := mkw 0xdba4062520006920 0x540202fdec800750 0xffffc00000007ffc 0x1c4000fffc000ff0

def z227 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000fc700071fc 0x03400000011001f0

def z228 : W := mkw 0xa481609010090049 0x8bccc2085b30a0aa 0xffc7fffffe3ff1ff 0xffffcf3c7ff1f1ff

def z229 : W := mkw 0x93a4000000000000 0xd40edbfdec000000 0xffffc00000000000 0x1c044bfffc000000

def z230 : W := mkw 0x025215600a905482 0x820c1862a30b0b05 0x00383f0001c00e00 0x000830c3820e0e00

def z231 : W := mkw 0x2401400010090049 0x09c000001000a0aa 0x000000000e3f8003 0x00b000000001f00f

def z232 : W := mkw 0x61488b0c86423210 0x79e3249314cccccc 0xe3f8c01f80077e3b 0x5d6384d39ce0cecc

def z233 : W := mkw 0x2148810082421210 0x09e000031408888c 0x03f8c00000000003 0x0c2000039c00000c

def z234 : W := mkw 0xa481400010090049 0x09c002085800a0aa 0xffc7c0fc700071ff 0xdf74403c7d1001ff

def z235 : W := mkw 0x000038da4d240000 0xa20dfd0003775000 0x03c73ffffffff1c3 0xfbffff2063fff10f

def z236 : W := mkw 0x0401400010090049 0x0000000000002022 0x000000e0703881c4 0x0010000001113133

def z237 : W := mkw 0x2401400010090049 0x09c000001000a0aa 0xe3c0c0fc7e3ff1ff 0xfff004101d11f1ff

def z238 : W := mkw 0x0200042000004000 0x820c1860a3000300 0x03ff3fe000007fc0 0xba4c38e3e3000f00

def z239 : W := mkw 0x0000104008000000 0x820c180003030000 0x00003f0001c00000 0x00083000020e0000

def z240 : W := mkw 0xa481400010090049 0x09c002085800a0aa 0xfc00c0fc7007f1fc 0xd744473c1d10f1f0

def z241 : W := mkw 0x0800042120004920 0x0000006400000310 0x1c000000000001c4 0x0000002c00000130

def z242 : W := mkw 0x2000000000000000 0x09c0000010008088 0xe000c01c00070038 0x450004101c00c0c0

def z243 : W := mkw 0xa48178da5d2d0049 0xabcdff085b77f0aa 0xfc00ffffffff803c 0xe78fff1c1ffff0f0

def z244 : W := mkw 0x61488b0c86423210 0xf9efe4f714cccccc 0xfff8ff1f8fc77e3b 0xffeff4ff9eeececc

def z245 : W := mkw 0xdba43eff6d246920 0xf60ffffdeff75750 0xfffffffffffffffc 0xffcffffffffffff0

def z246 : W := mkw 0x8481400010090049 0x0000020848002022 0xffc7c0e0703881c4 0xfc144f3c7d113133

def z247 : W := mkw 0xb7a5400010090049 0x5dc202fdfc00a0aa 0xffffc000000071ff 0x1c7000fffc0001ff

def z248 : W := mkw 0xeed377f53a997deb 0xdbcedafefbbbafff 0xffffffffffffffff 0xffffffffffffffff

def z249 : W := mkw 0x92a4000000000000 0x04001b08e8000000 0x0007000000000000 0x00000b0060000000

def z250 : W := mkw 0xa481400010090049 0x09c002085800a0aa 0x1c0700fc7e3ff1ff 0x03f44b2c6111f1ff

def z251 : W := mkw 0x480036f528006920 0xd20ed8f403b30750 0xfc003ffffff87ffc 0xf3cff8fc03ff0ff0

def z252 : W := mkw 0x000038da4d240000 0x2201e50003775000 0x00003fffffff8000 0x4383c70003fff000

def z253 : W := mkw 0xa481400010090049 0xd9cec2fc5800a0aa 0xffc7c0fc7e3ff1ff 0xffffcffc7d11f1ff

def z254 : W := mkw 0xa481400010090049 0x09c002085800a0aa 0xffc7c0e07038f1ff 0x1c744b3c7d1131ff

def z255 : W := mkw 0x132438da4d240000 0xf60ffdf5a7775000 0x00383f0381c00000 0x000bb0c382ee0000

def z256 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0xffffc00000000000 0x1c0bb0fffc000000

def z257 : W := mkw 0x4000062400006000 0xd20e00f003800740 0xe0003fff80007ff8 0xd34f80f003e00fc0

def z258 : W := mkw 0x6848afbda6427b30 0x0be0000213fccfdc 0x00003fffffc77fff 0x03e0000003fecffc

def z259 : W := mkw 0xb3ec890886421210 0xfdeffffffc4cc88c 0xffffc0000fc70003 0xfcaffffffc0ec00c

def z260 : W := mkw 0x000038da4d240000 0x2001fd0000775000 0x0000001fffff8000 0x6183ff0000fff000

def z261 : W := mkw 0x025211400a901482 0x00001802a00b0805 0x03ff00e00ff871c3 0xbaf43823e10f010f

def z262 : W := mkw 0x025215600a905482 0x820c1862a30b0b05 0x03ff3ffc7fffffc3 0xfbfc7fe3e31fff0f

def z263 : W := mkw 0x00523dfa4fb45482 0xa20dfd02037f5b05 0x00003fffffffffc3 0xe3ffff0003ffff0f

def z264 : W := mkw 0x0000080804000000 0x2001240000444000 0x00003f0381c00000 0x000bb00002ee0000

def z265 : W := mkw 0x605a9f6c8ed27692 0x0be0000213cfcfcd 0x00003fff8fff7ffb 0x03f0000003efcfcf

def z266 : W := mkw 0x61488b0c86423210 0x79e3249314cccccc 0xe038ff1f81c70e38 0x450bb4d39eeecec0

def z267 : W := mkw 0xb7a5400010090049 0x2dc13f09fc00a0aa 0xffffc0fc7e3ff1ff 0xfff47f3ffd11f1ff

def z268 : W := mkw 0x61488b0c86423210 0x79e3249314cccccc 0xe3ffffff8fff7ffb 0xffffbcf3ffefcfcf

def z269 : W := mkw 0x6948afbda6427b30 0xfbefe4f717fccfdc 0xe3f8ff1f8fc77e3b 0xffebb4d39eeececc

def z270 : W := mkw 0x6908aebda4426b30 0xfbefe4f517f4c7d8 0xfc00fffff0077ffc 0xd74fc4fc1ff0cff0

def z271 : W := mkw 0x2000000000000000 0x09c0000010008088 0x03c0c0000e070003 0x2ca004001c00c00c

def z272 : W := mkw 0x93a4184a4d240000 0xf40ffffdec475000 0xffffc0000fff8000 0xfc8ffffffc0ff000

def z273 : W := mkw 0x93a4042000004000 0xf60ffffdef000300 0xffffffe000007fc0 0xfe4fffffff000f00

def z274 : W := mkw 0x4000020400002000 0x0000000000800440 0x00003f1f80007e38 0x0340000002e00ec0

def z275 : W := mkw 0xdaa426b520006920 0xd60edbfcebb00750 0xfc073ffff0007ffc 0xd34fcbfc63f00ff0

def z276 : W := mkw 0x4000020400002000 0x5002009000800440 0xe000000000007e38 0x104000d000000ec0

def z277 : W := mkw 0xa481400010090049 0x09c002085800a0aa 0xffc7c01c0e0771ff 0xfff0043c7c00c1ff

def z278 : W := mkw 0x0000000000000000 0xa00dfd0000000000 0x0000000000000000 0x000bb00000000000

def z279 : W := mkw 0x000038da4d240000 0xa20dfd0003775000 0x00003fe3f1f88000 0x000ffb0003ff3000

def z280 : W := mkw 0x93a4000000000000 0x74033ffdec000000 0xffffc00000000000 0x3c003ffffc000000

def z281 : W := mkw 0x93a4080804000000 0xf40ffffdec444000 0xffffff1f8fc70000 0xff8ffffffeeec000

def z282 : W := mkw 0x00523dfa4fb45482 0x02000002037f5b05 0x00003fffffffffc3 0x03f0000003ffff0f

def z283 : W := mkw 0x4800062520006920 0x500200f400800750 0xfc003f1f80007ffc 0xd34b80fc02e00ff0

def z284 : W := mkw 0x025211400a901482 0x00001802a00b0805 0x03ff3f000ff87e03 0xbaf838c3e20f0e0f

def z285 : W := mkw 0x8080000000000000 0x0000020848000000 0xffc7c00000000000 0x1c00003c7c000000

def z286 : W := mkw 0x93a4000000000000 0xa40dff6dec000000 0x1fffc00000000000 0x2c047f2ffc000000

def z287 : W := mkw 0x2148994acf661210 0x29e13d03144fd88c 0x03f8c0000fff8003 0x2ca03f039c0ff00c

def z288 : W := mkw 0x0000289a45240000 0x2001e50000745000 0x00003f1fffc78000 0xe38bf70002fef000

def z289 : W := mkw 0x0140010002001000 0x7003249304080804 0xe3f8ff000fc07e03 0xfeebb4d39e0e0e0c

def z290 : W := mkw 0x6148830482423210 0x59e2009314888ccc 0xe3f8ff000fc07e3b 0xbee830d39e0e0ecc

def z291 : W := mkw 0xa481400010090049 0x09c002085800a0aa 0xffc7c0000e3ff1ff 0x3cf00f3c7c01f1ff

def z292 : W := mkw 0x000038da4d240000 0x820c180003775000 0x00003fffffff8000 0xa38c380003fff000

def z293 : W := mkw 0x0000209000000000 0x820cc00003300000 0x00003f0380000000 0x000b800002e00000

def z294 : W := mkw 0x6948a7b5a2427b30 0xdbeec0f717b88fdc 0xfff8fffff0007fff 0xdf6fc0ff9ff00ffc

def z295 : W := mkw 0x020038da4d240000 0xa20dfd60a3775000 0x03ff3fffffff8000 0xfb8fffe3e3fff000

def z296 : W := mkw 0x0000042000004000 0x820c006003000300 0xfc003ffc70007ffc 0xd34c40fc03100ff0

def z297 : W := mkw 0x8481400010090049 0x0000020848002022 0xfc0700fc7038f1fc 0xd3544b3c611131f3

def z298 : W := mkw 0x0000209000000000 0xa20dfd0003300000 0x00003ffff0000000 0xe30fff0003f00000

def z299 : W := mkw 0xa581400010090049 0x79c326995c00a0aa 0xffffc0fc7e3ff1ff 0xfffffffffd11f1ff

def z300 : W := mkw 0x61488b0c86423210 0x79e3249314cccccc 0x00383f1f8fc77e3b 0x03ebb0c382eececc

def z301 : W := mkw 0xb7a5400010090049 0x2dc13f09fc00a0aa 0x03ffc0000e3f8003 0x2cb03f03fc01f00f

def z302 : W := mkw 0x02523dfa4fb45482 0xa20dfd62a37f5b05 0x03ff3fe38ff87fc3 0xbaffb8e3e3ef0f0f

def z303 : W := mkw 0x9aa424b120004920 0x860cdb6ceb300310 0x1c0700e0700001c4 0x00044b2c61100130

def z304 : W := mkw 0x0000184a4d240000 0x20013d0000475000 0x000000fc7fff8000 0xe3847f00011ff000

def z305 : W := mkw 0x0000000000000000 0x2001e50000000000 0x0000000000000000 0x4003c70000000000

def z306 : W := mkw 0x025235f00a905482 0x820cd862a33b0b05 0x03ff3ffffff87fc3 0xfbfff8e3e3ff0f0f

def z307 : W := mkw 0xa481400010090049 0x09c002085800a0aa 0x03c7c0fc7e3ff1ff 0x2ff00f007d11f1ff

def z308 : W := mkw 0x0000104008000000 0x820c180003030000 0x000000e000380000 0x0004080001010000

def z309 : W := mkw 0x005215600a905482 0x02000002030b0b05 0x00003f0001c00e00 0x00000000020e0e00

def z310 : W := mkw 0x6000020400002000 0x59c20090108084c8 0xe3c0ff1f8e077e3b 0xffeb84d01ee0cecc

def z311 : W := mkw 0x02521d680e905482 0xa20d3c62a34f4b05 0x03ff3fff8fff7fc3 0xfbffbce3e3efcf0f

def z312 : W := mkw 0x91a4289a45240000 0x7403e79d4c745000 0xfc00c01ff0078000 0x4503c71c1cf0f000

def z313 : W := mkw 0x02523dfa4fb45482 0x820c1862a37f5b05 0x03ff3fffffffffc3 0xbbfc38e3e3ffff0f

def z314 : W := mkw 0xac8164b130094969 0x8bccc26c5b30a3ba 0xffc7c0fc7e3ff1ff 0xfff44f3c7d11f1ff

def z315 : W := mkw 0xec8166b530096969 0xdbcec2fc5bb0a7fa 0xffc7fffff0007fff 0xdf7fc0fc7ff00fff

def z316 : W := mkw 0x0200000000000000 0x800c1860a0000000 0x0038000000000000 0x000830c380000000

def z317 : W := mkw 0x080024b120004920 0x820cc06403300310 0x0000000000000000 0x0000000000000000

def z318 : W := mkw 0x8c8164b130094969 0x820cc26c4b302332 0x1c0700e0703881c4 0x00144b2c61113133

def z319 : W := mkw 0x025215600a905482 0x820c1862a30b0b05 0x00383fe00ff87fc3 0x02f830c3830f0f0f

def z320 : W := mkw 0x0000000000000000 0x0000000000000000 0x03c7000000000000 0xb804082060000000

def z321 : W := mkw 0x60488b0c86423210 0x59e2009210cccccc 0xe0003f1f8fc77e3b 0xd3eb80d002eececc

def z322 : W := mkw 0x035215600a905482 0xf20f3cf3a70b0b05 0xe3ffffe00ff87fc3 0xfeffbcf3ff0f0f0f

def z323 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000001c0e070000 0xe38004000000c000

def z324 : W := mkw 0x61488b0c86423210 0x79e3249314cccccc 0xe000ff1f8fc77e3b 0x47e384101eeececc

def z325 : W := mkw 0x0200000000000000 0x00001800a0000000 0x03ff000000000000 0x28003803e0000000

def z326 : W := mkw 0x4a5237f52a907da2 0xd20ed8f6a3bb0f55 0xfc383ffff1c07ffc 0xd34ff0ff83fe0ff0

def z327 : W := mkw 0x025215600a905482 0x02001802a30b0b05 0x03ff3fe00ff87fc3 0x2af03803e30f0f0f

def z328 : W := mkw 0x48003eff6d246920 0xa20dfd0003f75750 0x00003ffffffffffc 0xe3cfff0003fffff0

def z329 : W := mkw 0x025215600a905482 0x820c1862a30b0b05 0x03f83f000fc07e03 0xbae830c3820e0e0c

def z330 : W := mkw 0x000038da4d240000 0x0200000003775000 0x00003fffffff8000 0xe3844f0003fff000

def z331 : W := mkw 0x0212146008904482 0x820c1860a3030301 0x00073fe000387fc0 0x925c08e063010f03

def z332 : W := mkw 0x61488b0c86423210 0x79e3249314cccccc 0xe3f8fffffffffe3b 0xffefffd39ffffecc

def z333 : W := mkw 0x2108880884420210 0x29e124011444c088 0x0000c00000070000 0x040004001c00c000

def z334 : W := mkw 0x0000000000000000 0x0000000000000000 0xffc700fc7e3871ff 0xfbf4483c611101ff

def z335 : W := mkw 0x4800229520002920 0xd00ec0f400b00450 0xfc00001ff000003c 0xd10fc0fc00f000f0

def z336 : W := mkw 0x92f615600a905482 0x860cdb6eeb0b0b05 0x1fff3fe00ff87fc3 0xbafc7befe30f0f0f

def z337 : W := mkw 0x02521d6a4fb45482 0xa20d3d62a34f5b05 0x03ff3fe00fffffc3 0xbafc3fe3e30fff0f

def z338 : W := mkw 0x4800062520006920 0x0000000000800750 0x0000000000007ffc 0x0040000000000ff0

def z339 : W := mkw 0x08003cfb6d244920 0xa20dfd6403775310 0x1c003fffffff81c4 0xe38fff2c03fff130

def z340 : W := mkw 0x0000000000000000 0x800c180000000000 0x0000000000000000 0xa00c380000000000

def z341 : W := mkw 0xa481480814090049 0x29c126085844e0aa 0xffc7fffffffff1ff 0xffffff3c7ffff1ff

def z342 : W := mkw 0x635a9b4c8ed23692 0x79e33c93b4cfcccd 0xe3ffff1f8fff7e3b 0xfffbbcd3feefcecf

def z343 : W := mkw 0x0000042000004000 0xd20ec0f403000300 0xfc003fe000007fc0 0xd24fc0fc03000f00

def z344 : W := mkw 0x93a430d249240000 0xf60ffffdef331000 0xffffc0e070388000 0xfc0ffffffd113000

def z345 : W := mkw 0x8080000000000000 0x0000020848000000 0xfc00c00000000000 0x4400471c1c000000

def z346 : W := mkw 0xa481584a5d2d0049 0x29c13f085847f0aa 0xffc7c0fc7ffff1ff 0xfff47f3c7d1ff1ff

def z347 : W := mkw 0xa481400010090049 0x09c002085800a0aa 0xffc7c01c7e3f803f 0x6db04f1c7c11f0ff

def z348 : W := mkw 0x8080000000000000 0x0000020848000000 0xffc7c0e00e3871c3 0xfef44f3c7d01010f

def z349 : W := mkw 0x000030d249240000 0x820cd90003331000 0x000000fc7e3f8000 0xe3844f000111f000

def z350 : W := mkw 0x4800020520002920 0x5002009400800450 0xfc0000000000003c 0x0000001c000000f0

def z351 : W := mkw 0x91a4000000000000 0x7403e79d4c000000 0xffc7c00000000000 0xfc07cf3c7c000000

def z352 : W := mkw 0x0100000000000000 0x7003249104000000 0x0038000000000000 0x000bb0c380000000

def z353 : W := mkw 0x000030d249240000 0xa20dfd0003331000 0x000000e070388000 0xe00fff0001113000

def z354 : W := mkw 0x0000000000000000 0x0000000000000000 0xfc0000fc7e3ff1fc 0xf3c44f3c0111f1f0

def z355 : W := mkw 0x0000042000004000 0x820c006003000300 0x00003f0000000e00 0x000800c002000e00

def z356 : W := mkw 0x000038da4d240000 0xf20ffdf403775000 0xfc003fffffff8000 0xf38ffffc03fff000

def z357 : W := mkw 0x93a4000000000000 0x74033f99ec000000 0xe3ffc00000000000 0xfc0bbfd3fc000000

def z358 : W := mkw 0x93f611400a901482 0x24013f0bec0b0805 0x03ffc0000ff80003 0x2cb03f03fc0f000f

def z359 : W := mkw 0x0040010002001000 0x0000000200080804 0x03ff3fe00ff87fc3 0xbafc38e3e30f0f0f

def z360 : W := mkw 0x6c0166b530096969 0xdbcec0f413b0a7fa 0xfc003ffffe3fffff 0xd3ffc0fc03f1ffff

def z361 : W := mkw 0xc88026b520006920 0xd20ec2fc4bb00750 0xffc7fffff0007ffc 0xff4fcffc7ff00ff0

def z362 : W := mkw 0x0000000000000000 0xf00ffdf400000000 0xfc00000000000000 0xf00ffffc00000000

def z363 : W := mkw 0x0300000000000000 0xf00f3cf1a4000000 0xe3ffc00000000000 0xfc0fbcf3fc000000

def z364 : W := mkw 0x0000289a45240000 0x2001e50000745000 0x000000fffe3f8000 0xe387cf0001f1f000

def z365 : W := mkw 0x6048bbdecf663210 0x0be0000213ffdccc 0x00003ffffffffe3b 0x03e0000003fffecc

def z366 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0xffffc0fc7e3f8000 0xff8ffffffd11f000

def z367 : W := mkw 0x240178da5d2d0049 0x0bc000001377f0aa 0x00003ffffffff1ff 0x03f0000003fff1ff

def z368 : W := mkw 0x000038da4d240000 0x820cd90003775000 0x00003fffffff8000 0x03844b0003fff000

def z369 : W := mkw 0x0100080804000000 0x7003249104444000 0xe3f8ff1f8fc70000 0xff8bb4d39eeec000

def z370 : W := mkw 0x4a5237f52a907da2 0x820c1862a3bb0f55 0x03ff3ffffff87fff 0xbbfc38e3e3ff0fff

def z371 : W := mkw 0xa481400010090049 0x09c002085800a0aa 0x03c7c00000000003 0x0c3000007c00000f

def z372 : W := mkw 0x4800229520002920 0x5002c09400b00450 0x0000000380000000 0x0003800000e00000

def z373 : W := mkw 0xf7edcb0c964b3259 0xfdeffffffcccecee 0xffffffffffffffff 0xffffffffffffffff

def z374 : W := mkw 0x6048830482423210 0x09e0000210888ccc 0x0000000000007e3b 0x0060000000000ecc

def z375 : W := mkw 0xa481400010090049 0x09c002085800a0aa 0x0000c00000078000 0x040007001c00f000

def z376 : W := mkw 0xf1ac8a0c84422210 0x7de3e79d5cc4c4c8 0xfc00c01f80070038 0x4503c71c1ce0c0c0

def z377 : W := mkw 0x02123cfa4db44482 0xa20dfd60a3775301 0x00073fffffff81c0 0xe39fff2063fff103

def z378 : W := mkw 0x4a5217652a907da2 0xd20e18f6a38b0f55 0xffff3fe00ff87fff 0xbafc38ffe30f0fff

def z379 : W := mkw 0xe7dbdf6c9edb76db 0xfbef3efbffcfefef 0xffffffffffffffff 0xffffffffffffffff

def z380 : W := mkw 0x025215600a905482 0x820c1862a30b0b05 0x03ff00e00ff801c3 0x28b43823e10f010f

def z381 : W := mkw 0x6908aa9da4422b30 0x79e3e49514f4c4d8 0xfc00c01ff007003c 0x4503c41c1cf0c0f0

def z382 : W := mkw 0x025211400a901482 0x800c1862a00b0805 0x03ff00000ff80003 0xb8bc38e3e00f000f

def z383 : W := mkw 0x200038da4d240000 0xabcdfd001377d088 0xe3c0fffffffff03b 0xffefff101ffff0cc

def z384 : W := mkw 0x005215600a905482 0x820c1802030b0b05 0x00003fe00ff87fc3 0xa2fc3800030f0f0f

def z385 : W := mkw 0x4a52072522907da2 0x500200f6a0880f55 0xffff000000007fff 0x187000ffe0000fff

def z386 : W := mkw 0x080024b120004920 0x0200000003300310 0x000000e0700001c4 0x0000000001100130

def z387 : W := mkw 0x0200000000000000 0xd00ed8f4a0000000 0xffff000000000000 0xf80ff8ffe0000000

def z388 : W := mkw 0x0252052002905482 0x00000062a0080b05 0x0038000000000e00 0x000000c380000e00

def z389 : W := mkw 0x480026b520006920 0x820c006003b00750 0x00003ffff0007ffc 0x934c00e003f00ff0

def z390 : W := mkw 0x0052052002905482 0x0000000200080b05 0x0000000000007fc3 0x0070000000000f0f

def z391 : W := mkw 0xa481400010090049 0x09c002085800a0aa 0xffc7c01c7007803c 0xfd044f3c7c10f0f0

def z392 : W := mkw 0x8481400010090049 0x0000020848002022 0x1c0700fc7e3f81c4 0xe3944f2c6111f133

def z393 : W := mkw 0x48003eff6d246920 0xf20ffdf403f75750 0x00003fffffff8e00 0xe38fffc003fffe00

def z394 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000e3f8000 0x20800f000001f000

def z395 : W := mkw 0x93a4184a4d240000 0x24013f09ec475000 0x03ffc0000fff8000 0x2c803f03fc0ff000

def z396 : W := mkw 0xa481400010090049 0x09c002085800a0aa 0xffc7c01c7007f1ff 0x5d70473c7c10f1ff

def z397 : W := mkw 0x4800062520006920 0x500200f400800750 0x0000000000000e00 0x000000c000000e00

def z398 : W := mkw 0x0000289a45240000 0xa20de50003745000 0x00003ffff0078000 0xc30fc70003f0f000

def z399 : W := mkw 0x0200000000000000 0xa00dfd60a0000000 0x03ff000000000000 0xf80fffe3e0000000

def z400 : W := mkw 0x48003adf6d242920 0xf20ffd9403f75450 0xfc003fffffff803c 0xe38fff1c03fff0f0

def z401 : W := mkw 0x0212104008900482 0x00001800a0030001 0x0007000000380000 0x0010080060010003

def z402 : W := mkw 0x0000184a4d240000 0xa20d3d0003475000 0x00003fe00fff8000 0xa28c3f00030ff000

def z403 : W := mkw 0x48002a9f65242920 0x7003e59400f45450 0xfc00001ff007803c 0x4103c71c00f0f0f0

def z404 : W := mkw 0x0040052002005000 0x820c006203080b04 0x03f83fe00fc07fc3 0xbaec30e3830e0f0c

def z405 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000fc70000000 0xc304400001100000

def z406 : W := mkw 0x92a430d249240000 0x860cdb6ceb331000 0x1c0700e070388000 0x00044b2c61113000

def z407 : W := mkw 0x6108820480422210 0x59e20091148084c8 0xe000c00000000038 0x040000101c0000c0

def z408 : W := mkw 0x4000020400002000 0xd00ec0f400800440 0xfc003f1f80007e38 0xd34fc0fc02e00ec0

def z409 : W := mkw 0x0000080804000000 0x2001240000444000 0x000000000fc70000 0x20803400000ec000

def z410 : W := mkw 0xa48170d2592d0049 0x8bccdb085b33b0aa 0xffc7c0fc7e3ff1ff 0xfff44f3c7d11f1ff

def z411 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0xfc38c00000000000 0x440bf7df9c000000

def z412 : W := mkw 0x0000080804000000 0xa00dfd0000444000 0x00003f1f8fc70000 0xe38fff0002eec000

def z413 : W := mkw 0x000038da4d240000 0xa20dfd0003775000 0x00003fffffff8000 0x038bb00003fff000

def z414 : W := mkw 0x5b2426b520006920 0xf60ffdf5a7b00750 0xfc383ffff0007ffc 0xd34ff0ff83f00ff0

def z415 : W := mkw 0x025235f24bb45482 0x820cd962a33b1b05 0x03ff3fe07ff8ffc3 0xbafc7be3e31f3f0f

def z416 : W := mkw 0x0200104008000000 0x820c1860a3030000 0x03ff3fe00ff80000 0xba8c38e3e30f0000

def z417 : W := mkw 0x2401400010090049 0x09c000001000a0aa 0x0000001c7007803c 0x010000000010f0f0

def z418 : W := mkw 0x0000209000000000 0x820cc00003300000 0xfc003ffff00071fc 0xd34fc03c03f001f0

def z419 : W := mkw 0x0000000000000000 0x800c006000000000 0x0000000000000000 0x900c00e000000000

def z420 : W := mkw 0x025239da4fb41482 0xa20dfd02a37f5805 0x03ff3fffffff8003 0xebbfff03e3fff00f

def z421 : W := mkw 0xa6d351401a9914cb 0x09c01a0af80ba8af 0xffffc0fc7ffff1ff 0xfff47f3ffd1ff1ff

def z422 : W := mkw 0xa4c1410012091049 0x09c0020a5808a8ae 0xfffffffc7fffffff 0xfffc7fffff1fffff

def z423 : W := mkw 0x93f615600a905482 0xf60fffffef0b0b05 0xffffff0001c00e00 0xfc0ffffffe0e0e00

def z424 : W := mkw 0x61488b0c86423210 0x59e2009314cccccc 0xe3f8ff1f8fc77e3b 0x1fe000d39eeececc

def z425 : W := mkw 0x000030d249240000 0x820cd90003331000 0x00003fe07ff88000 0xa28c7b00031f3000

def z426 : W := mkw 0x0000000000000000 0x5002009000000000 0xe000000000000000 0xd00b80d000000000

def z427 : W := mkw 0x86d355601a9954cb 0x820c1a6aeb0b2b27 0x1fff3fe07ff8ffc7 0xbafc7befe31f3f3f

def z428 : W := mkw 0x48003eff6d246920 0xd20ec0f403f75750 0xfc003ffffffffffc 0xd3cfc0fc03fffff0

def z429 : W := mkw 0x0100000000000000 0xf00fe4f504000000 0xfff8c00000000000 0xfc0ff4ff9c000000

def z430 : W := mkw 0x025215600a905482 0x820c1862a30b0b05 0xffff3ffc7ff87fff 0xfbfc78ffe31f0fff

def z431 : W := mkw 0x0200000000000000 0x00000060a0000000 0x03ff000000000000 0x180000e3e0000000

def z432 : W := mkw 0x025215600a905482 0x02000062a30b0b05 0x03ff3fe00ff87fc3 0x1af000e3e30f0f0f

def z433 : W := mkw 0xd3ec8b0c86423210 0xf42fffffeccc4c44 0xffffff0381c00e00 0xfc0ffffffeee0e00

def z434 : W := mkw 0x635abffecff67692 0xfbeffdf3b7ffdfcd 0xe3fffffffffffffb 0xfffffff3ffffffcf

def z435 : W := mkw 0x0000104249240000 0x0000190000031000 0x0000000000388000 0x00000b0000013000

def z436 : W := mkw 0x425217640a907482 0xd20e18f2a38b0f45 0xe3ff3fff8ff87ffb 0xfbffb8f3e3ef0fcf

def z437 : W := mkw 0x000038da4d240000 0xa20dfd0003775000 0x000000e07fff8000 0x20847f00011ff000

def z438 : W := mkw 0xec8166b530096969 0x0bc002085bb0a7fa 0xffc7fffffe3fffff 0xfff44f3c7ff1ffff

def z439 : W := mkw 0x000038da4d240000 0x820cc00003775000 0x00003fffffff8000 0xc38fc00003fff000

def z440 : W := mkw 0xe5c9c304924b3259 0x59e2029b5c88acee 0xffffc0fc7e3fffff 0xfff44ffffd11ffff

def z441 : W := mkw 0x000038da4d240000 0xa20dfd0003775000 0x00003fe38ff80000 0xa28fb80003ef0000

def z442 : W := mkw 0xa5c9c908964b1259 0x29e1260b5c4ce8ae 0x03ffc0000fff8003 0x2cb03f03fc0ff00f

def z443 : W := mkw 0x480026b520006920 0xd20ec0f403b00750 0x00003ffff0007ffc 0x034b80c003f00ff0

def z444 : W := mkw 0x005211400a901482 0x00000002000b0805 0x000000000ff80003 0x00b00000000f000f

def z445 : W := mkw 0x60488b0c86423210 0x29e1240210cccccc 0x00003f1f8fc77e3b 0xe3ebb40002eececc

def z446 : W := mkw 0x2401400010090049 0x09c000001000a0aa 0x03c700fc7e3ff1ff 0xbbf408206111f1ff

def z447 : W := mkw 0xe5c9cb0c964b3259 0x79e3269b5cccecee 0xfff8ff1fffc7fe3f 0xffebf7df9efefefc

def z448 : W := mkw 0x2000080804000000 0x29c124001044c088 0xe3c0ff1f8fc7703b 0xffebb4101eeec0cc

def z449 : W := mkw 0x480026b520006920 0x820cc06403b00750 0x1c003ffff0007ffc 0x0344402c03f00ff0

def z450 : W := mkw 0x02523dfa4fb45482 0xa20dfd62a37f5b05 0x00383f0381c00e00 0x000bb0c382ee0e00

def z451 : W := mkw 0x0000184a4d240000 0x20013d0000475000 0x0000000001c00000 0x00003000000e0000

def z452 : W := mkw 0xec81462530096969 0x59c202fc5880a7fa 0xffc7c0fc7e3fffff 0xfff44ffc7d11ffff

def z453 : W := mkw 0xf3ec830482423210 0xfdeffffffc888ccc 0xffffc00000007e3b 0xfc6ffffffc000ecc

def z454 : W := mkw 0x4800062520006920 0xd00ec0f400800750 0xfc00000000007ffc 0xd04fc0fc00000ff0

def z455 : W := mkw 0xf3ecbbdecf663210 0xffefffffffffdccc 0xfffffffffffffe3b 0xffeffffffffffecc

def z456 : W := mkw 0xb6a5400010090049 0x8dccdb6cf800a0aa 0xffc7c0fc7e3ff1ff 0xfff44f3c7d11f1ff

def z457 : W := mkw 0x92a4000000000000 0xa40dff6ce8000000 0x1c07000000000000 0xe00fff2c60000000

def z458 : W := mkw 0x61489b4c8e423210 0xfbef3c9317cfcccc 0xe3f8ffff8fff7e3b 0xffefbcd39fefcecc

def z459 : W := mkw 0x93f63dfa4fb45482 0xf60fffffef7f5b05 0xffffffffffffffc3 0xffffffffffffff0f

def z460 : W := mkw 0xa681400010090049 0x89cc1a68f800a0aa 0xffffc0fc7e3ff1ff 0xfffc7ffffd11f1ff

def z461 : W := mkw 0x93a4000000000000 0x7403e7fdec000000 0xffffc00000000000 0x5c03c7fffc000000

def z462 : W := mkw 0x4148830482423210 0x5022009304880c44 0x0038000000000e00 0x000000c380000e00

def z463 : W := mkw 0x8080000000000000 0x0000020848000000 0xffc7c0fc7e3f8000 0xff844f3c7d11f000

def z464 : W := mkw 0xf3ec830482423210 0x5de202fffc888ccc 0xffffc00000007e3b 0x1c6000fffc000ecc

def z465 : W := mkw 0x480026b520006920 0x0200000003b00750 0xfc003ffff0007ffc 0xd344403c03f00ff0

def z466 : W := mkw 0x6549cb0c964b3259 0x79e3249314ccecee 0xe3f8ffffffffffff 0xfffbb4d39fffffff

def z467 : W := mkw 0x480036f769246920 0xd20ed9f403b31750 0xfc003ffff038fffc 0xd34fcbfc03f13ff0

def z468 : W := mkw 0xa481400010090049 0x09c002085800a0aa 0xffc7c0fc7e3ff1ff 0x1ff0003c7d11f1ff

def z469 : W := mkw 0xf3ec8b0c86423210 0x7de326fffccccccc 0xffffff1f8fc77e3b 0xffebb4fffeeececc

def z470 : W := mkw 0xa6935460189944cb 0x8bcc1a68fb03a3ab 0xffc7c0fc7e3ff1ff 0xfff44f3c7d11f1ff

def z471 : W := mkw 0x92a438da4d240000 0xa60dff6ceb775000 0x1c073fffffff8000 0xe38fff2c63fff000

def z472 : W := mkw 0x000038da4d240000 0x0200000003775000 0x00003f0381c00000 0x0000000002ee0000

def z473 : W := mkw 0x0100000000000000 0x5002009104000000 0xe3f8c00000000000 0x1c0000d39c000000

def z474 : W := mkw 0x848170d2592d0049 0x820cdb084b333022 0x1c0700e0703881c4 0x00144b2c61113133

def z475 : W := mkw 0x92a4000000000000 0xd40edbfce8000000 0xfc07000000000000 0xd00fcbfc60000000

def z476 : W := mkw 0x8080000000000000 0x0000020848000000 0x03c7c00000000000 0x2c000f007c000000

def z477 : W := mkw 0x025215600a905482 0x820c1862a30b0b05 0x00383fe001c07fc0 0x924c30e3830e0f00

def z478 : W := mkw 0x000038da4d240000 0x2201240003775000 0x00003fffffff8000 0xe38bb40003fff000

def z479 : W := mkw 0xa481504018090049 0x8bcc1a085b03a0aa 0xffc7fffc7ffff1ff 0xfffc7f3c7f1ff1ff

def z480 : W := mkw 0x63488b0c86423210 0xf9ef3cf3b4cccccc 0xe3ffff1f8fc77e3b 0xffefbcf3feeececc

def z481 : W := mkw 0x0000000000000000 0x0000000000000000 0x1c0000e0700001c4 0x0004402c01100130

def z482 : W := mkw 0x0000184a4d240000 0xa00dfd0000475000 0x000000000fff8000 0xe08fff00000ff000

def z483 : W := mkw 0x0000000000000000 0x0000000000000000 0xfc00001c7000003c 0x4100401c001000f0

def z484 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000e00e3871c3 0x02f000000101010f

def z485 : W := mkw 0x080024b120004920 0xd20ec0f403300310 0xfc0000e0700001c4 0xd00fc0fc01100130

def z486 : W := mkw 0xb3a4000000000000 0xfdcffffdfc008088 0xffffc01c0e07703b 0xffeffffffc00c0cc

def z487 : W := mkw 0x2000000000000000 0x09c0000010008088 0xe3c0c0fc7e3ff03b 0xffe44f101d11f0cc

def z488 : W := mkw 0x000038da4d240000 0xa20dfd0003775000 0x00003f1ff1c78000 0x410bf70002fef000

def z489 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000e070388000 0x00044b0001113000

def z490 : W := mkw 0x000030d249240000 0x820cd90003331000 0x0000000000000000 0x0000000000000000

def z491 : W := mkw 0x0040010002001000 0x0000000200080804 0x03f800000fc00003 0x28a03003800e000c

def z492 : W := mkw 0x435a9f6c8ed27692 0xf22f3cf3a7cf4f45 0x00383f0381c00e00 0x000bb0c382ee0e00

def z493 : W := mkw 0x93f615600a905482 0xa60d3f6bef0b0b05 0x03ffffe00ff87fc3 0xbefc3fe3ff0f0f0f

def z494 : W := mkw 0x0252052002905482 0x00000062a0080b05 0x03ff3f000fc07fc3 0xbaf830e3e20e0f0f

def z495 : W := mkw 0xa481400010090049 0xa9cdff085800a0aa 0xffc7c0fc7e3ff1ff 0xffffff3c7d11f1ff

def z496 : W := mkw 0xa6d355601a9954cb 0x8bcc1a6afb0babaf 0xffffffe00ff87fff 0xbefc38ffff0f0fff

def z497 : W := mkw 0x005215600a905482 0x820c0062030b0b05 0x00003fe00ff87fc3 0x92fc00e0030f0f0f

def z498 : W := mkw 0x025215600a905482 0x820c1862a30b0b05 0x03ff3f0001c07fc3 0x187830e3e20e0f0f

def z499 : W := mkw 0x480026b520006920 0xd20ec0f403b00750 0x1c003fe3f0000fc4 0x000fc0ec03f00f30

def z500 : W := mkw 0x61488b0c86423210 0x79e3249314cccccc 0xe3f8c0000fc77e3b 0x3ce034d39c0ececc

def z501 : W := mkw 0x536c8b0c86423210 0xf42ffdf7a4cc4c44 0x00383f0381c00e00 0x000bb0c382ee0e00

def z502 : W := mkw 0x005215600a905482 0x02000002030b0b05 0x03c73fe00ff87fc3 0xbaf40820630f0f0f

def z503 : W := mkw 0x48003eff6d246920 0x0200000003f75750 0x00003ffffffffffc 0x03c0000003fffff0

def z504 : W := mkw 0x000024b000004000 0x820cc06003300300 0x00003ffff0007fc0 0xd34fc0e003f00f00

def z505 : W := mkw 0x480026b520006920 0xd20ec0f403b00750 0xfc003f1ff0000e3c 0x410bc0dc02f00ef0

def z506 : W := mkw 0x480026b520006920 0xd20ec0f403b00750 0xfc0000fff00001fc 0x4107c03c01f001f0

def z507 : W := mkw 0x235a99488ed21692 0x29e13c03b44fc88d 0x03ffc0000fff0003 0x2cb03c03fc0fc00f

def z508 : W := mkw 0x2048890886421210 0x09e00002104cc88c 0x000000000fc70003 0x00a00000000ec00c

def z509 : W := mkw 0x000038da4d240000 0x22013d0003775000 0x00003fffffff8000 0x23803f0003fff000

def z510 : W := mkw 0x0000146008004000 0x820c186003030300 0x00003fe00ff87fc0 0xb2cc38e0030f0f00

def z511 : W := mkw 0x48002ebd24006920 0xf20fe4f403f44750 0xfc003fffffc77ffc 0xf3cff4fc03fecff0

def z512 : W := mkw 0xa481400010090049 0x09c002085800a0aa 0xffc7c0000e3f8003 0xfcb44f3c7c01f00f

def z513 : W := mkw 0x61488b0c86423210 0xf9effd9314cccccc 0xe3f8ff1f8fc77e3b 0xffefffd39eeececc

def z514 : W := mkw 0xffa566b530096969 0xffcffffdffb0a7fa 0xfffffffffe3fffff 0xfffffffffff1ffff

def z515 : W := mkw 0xb7a5400010090049 0x5dc202fdfc00a0aa 0xffffc0fc7e3ff1ff 0xfff44ffffd11f1ff

def z516 : W := mkw 0x61088a0c84422210 0x79e3249114c4c4c8 0xe000ff1f80077e38 0xd74b84d01ee0cec0

def z517 : W := mkw 0xec81629530092969 0x59c2c29c58b0a4fa 0xfc00c01ff007803c 0x4503c71c1cf0f0f0

def z518 : W := mkw 0x6449cb0c964b3259 0x09e0000210ccecee 0x00003fffffffffff 0x03f0000003ffffff

def z519 : W := mkw 0x435a9f6c8ed27692 0xf22f3cf3a7cf4f45 0x03ff3fe38ff87fc3 0xbaffb8e3e3ef0f0f

def z520 : W := mkw 0x080024b120004920 0x820cc06403300310 0x1c003ffff00001c4 0xc30fc02c03f00130

def z521 : W := mkw 0xf3ec8b0c86423210 0x7de33f9bfccccccc 0xe3ffff1f8fc77e3b 0xffebbfd3feeececc

def z522 : W := mkw 0x0000000000000000 0x5002c09400000000 0xfc00000000000000 0x4003c01c00000000

def z523 : W := mkw 0xa481400010090049 0x09c002085800a0aa 0xfc00c0000000003c 0x0400001c1c0000f0

def z524 : W := mkw 0x4800062520006920 0xd20e00f403800750 0xfc003fe000007ffc 0x924c00fc03000ff0

def z525 : W := mkw 0x1324000000000000 0xf40ffdf5a4000000 0x0038000000000000 0xe00fffc380000000

def z526 : W := mkw 0x0000042000004000 0x0200000003000300 0x00003fe000007fc0 0x0240000003000f00

def z527 : W := mkw 0xb5a5400010090049 0x7dc3e79d5c00a0aa 0xfc00c01c7007803c 0x4503c71c1c10f0f0

def z528 : W := mkw 0x484027b522007920 0xd20ec0f603b80f54 0xfff83fffffc07fff 0xfbeff0ff83fe0ffc

def z529 : W := mkw 0x61488b0c86423210 0x29e1240314cccccc 0x03f8ff1f8fc77e3b 0x2fe034039eeececc

def z530 : W := mkw 0x96a5400010090049 0x840cdb6ce8002022 0x1c0700e0703881c4 0x00144b2c61113133

def z531 : W := mkw 0x4148bbdecf663210 0xf22ffd9307ff5c44 0x00383f0381c00e00 0x000bb0c382ee0e00

def z532 : W := mkw 0x6148ab9ec7663210 0x79e3e59314fcdccc 0xe3f8ff1fffc7fe3b 0xffebf7d39efefecc

def z533 : W := mkw 0x91a4000000000000 0xf40fff9d4c000000 0xfc00c00000000000 0xe40fff1c1c000000

def z534 : W := mkw 0x848178da5d2d0049 0xa20dff084b777022 0x1c073fffffff81c4 0xe39fff2c63fff133

def z535 : W := mkw 0x48002ebf65246920 0xf20fe5f403f45750 0xfc003ffff007fffc 0xd34fc7fc03f0fff0

def z536 : W := mkw 0x0000289a45240000 0x0000000000745000 0x0000001ff0078000 0x0100000000f0f000

def z537 : W := mkw 0x4a5227b522907da2 0xd20ec0f6a3b80f55 0xffff3ffff0007fff 0xdb7fc0ffe3f00fff

def z538 : W := mkw 0x61088a0c84422210 0x79e3249114c4c4c8 0xe3f8c01f80070038 0xfd0bb4d39ce0c0c0

def z539 : W := mkw 0x490026b520006920 0xf20fe4f507b00750 0xfff8fffff0007ffc 0xff4ff4ff9ff00ff0

def z540 : W := mkw 0x0800209120000920 0x0000c00400300010 0x1c00000070000004 0x0000400c00100030

def z541 : W := mkw 0xb7a5400010090049 0xfdcffffdfc00a0aa 0xffffc0000e3f8003 0xfcbffffffc01f00f

def z542 : W := mkw 0x0000209000000000 0x820cc00003300000 0x000000e070000000 0x0004400001100000

def z543 : W := mkw 0xa481400010090049 0x09c002085800a0aa 0xfc07c0fc703f81fc 0x45144f3c7d11f1f3

def z544 : W := mkw 0x91a438da4d240000 0xf60fff9d4f775000 0xfc00ffffffff8000 0xe78fff1c1ffff000

def z545 : W := mkw 0x6948bfffef667b30 0xfbeffdf717ffdfdc 0xfff8ffffffffffff 0xffefffff9ffffffc

def z546 : W := mkw 0x0000000000000000 0x20013d0000000000 0x0000000000000000 0x20003f0000000000

def z547 : W := mkw 0x480026b520006920 0xd20ec0f403b00750 0x00003fe380007fc0 0x924f80e003e00f00

def z548 : W := mkw 0x60488b0c86423210 0x09e0000210cccccc 0xe3c0ff1f8fc77e3b 0xffe004101eeececc

def z549 : W := mkw 0x4000229400002000 0xd20ec09003b00440 0xe0003ffff0007e38 0xd34fc0d003f00ec0

def z550 : W := mkw 0x480026b520006920 0xf20ffdf403b00750 0xfc003ffff0007ffc 0xf34ffffc03f00ff0

def z551 : W := mkw 0xa481584a5d2d0049 0x29c13f085847f0aa 0x03c7c0000fff8003 0x2cb03f007c0ff00f

def z552 : W := mkw 0x0000104008000000 0x0200000003030000 0x00003fe00ff80000 0x02800000030f0000

def z553 : W := mkw 0x1324000000000000 0x24013d01a4000000 0x0038000000000000 0x0000300380000000

def z554 : W := mkw 0xd3a4020400002000 0xf40ffffdec800440 0xffffff1f80007e38 0xff4ffffffee00ec0

def z555 : W := mkw 0xa481689a552d0049 0x29c1e7085874f0aa 0xfc00c01ff007803c 0x4503c71c1cf0f0f0

def z556 : W := mkw 0x97a5400010090049 0xf40ffffdec002022 0xffffc0e0703881c4 0xfc1ffffffd113133

def z557 : W := mkw 0x4948afbda6427b30 0xf22fe4f707fc4f54 0x00383f0381c00e00 0x000bb0c382ee0e00

def z558 : W := mkw 0xa5c9c908964b1259 0x29e1260b5c4ce8ae 0xffffc0fc7ffff1ff 0xfff47f3ffd1ff1ff

def z559 : W := mkw 0x0252052002905482 0x00000062a0080b05 0x03ff00e00e387fc3 0xbaf408e3e1010f0f

def z560 : W := mkw 0x0000000000000000 0x0000000000000000 0x00003f000fc00000 0xa2883000020e0000

def z561 : W := mkw 0x0000104008000000 0x820c180003030000 0x03c73fe00ff871c3 0xbafc3820630f010f

def z562 : W := mkw 0x0212146008904482 0x820c1860a3030301 0x0000000000000000 0x0000000000000000

def z563 : W := mkw 0x8080000000000000 0x0000020848000000 0x1c07000000000000 0x00044b2c60000000

def z564 : W := mkw 0x92b6146008904482 0x860cdb6ceb030301 0x1c0700e0003801c0 0x00144b2c61010103

def z565 : W := mkw 0x736c8b0c86423210 0xfdeffdf7b4cccccc 0xe3f8ff1f8fc77e3b 0xffebb4d39eeececc

def z566 : W := mkw 0xa6d34520129954cb 0x09c0026af808abaf 0xffffc0fc7e3fffff 0xfff44ffffd11ffff

def z567 : W := mkw 0x4040030402003000 0x5002009200880c44 0xe3f83f1f8fc07e3b 0xfbebb0d382ee0ecc

def z568 : W := mkw 0x0000104008000000 0x820c180003030000 0x00003ffc7fff8000 0xe38c7f00031ff000

def z569 : W := mkw 0x137615600a905482 0xf60ffdf7a70b0b05 0x03ff3fe00ff87fc3 0xbaffb8e3e30f0f0f

def z570 : W := mkw 0x91a4000000000000 0xf40fe7fd4c000000 0xfc00c00000000000 0xd40fc7fc1c000000

def z571 : W := mkw 0x025215600a905482 0xd20ed8f6a30b0b05 0xffff3fe00ff87fc3 0xfafff8ffe30f0f0f

def z572 : W := mkw 0xd9a4229520002920 0x7403e79d4cb00450 0xfc00c01ff000003c 0x4503c71c1cf000f0

def z573 : W := mkw 0x61488b0c86423210 0x79e3249314cccccc 0xfff8ffffffc77fff 0xffeff4ff9ffecffc

def z574 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000e0000071c0 0x9244002001000100

def z575 : W := mkw 0xf3fe9f6c8ed27692 0xffefffffffcfcfcd 0xffffffff8fff7ffb 0xffffffffffefcfcf

def z576 : W := mkw 0x6148bbdecf663210 0xfbeffd9317ffdccc 0xe3f8ff1f8fc77e3b 0xffebb4d39eeececc

def z577 : W := mkw 0x000018480c000000 0xa20d3c0003474000 0x00003fff8fff0000 0xe38fbc0003efc000

def z578 : W := mkw 0x0000000000000000 0x0000000000000000 0xe000001c00007038 0xd3400010000000c0

def z579 : W := mkw 0x025215600a905482 0x820c1862a30b0b05 0x003f3fe001f80fc0 0x001c38e3e30f0f03

def z580 : W := mkw 0x808038da4d240000 0xa20dff084b775000 0xffc7ffffffff8000 0xff8fff3c7ffff000

def z581 : W := mkw 0x40003ade4d242000 0xf20ffd9003f75440 0xe0003ffffffffe38 0xf3cfffd003fffec0

def z582 : W := mkw 0xa4d355601a9954cb 0x0bc0020a5b0babaf 0xffc7fffc7fffffff 0xfff44f3c7f1fffff

def z583 : W := mkw 0x225215600a905482 0x8bcc1862b30b8b8d 0xe3fffffc0fff7ffb 0xfffc3cf3ff0fcfcf

def z584 : W := mkw 0x004039da4f241000 0xa20dfd02037f5804 0x03f83ffffffffe03 0xfbefffc383fffe0c

def z585 : W := mkw 0x4800229520002920 0x5002c09400b00450 0xfc0000fff00071fc 0xd347c03c01f001f0

def z586 : W := mkw 0x4800229520002920 0xd20ec09403b00450 0xfc003ffff000003c 0xc30fc01c03f000f0

def z587 : W := mkw 0x635a872482d27692 0x59e200f3b4888fcd 0xe3ffc00000007ffb 0x1c7000f3fc000fcf

def z588 : W := mkw 0x0000000000000000 0x0000000000000000 0x000700e0003801c0 0x0014082061010103

def z589 : W := mkw 0x625a9f6c8ed27692 0x8bec1862b3cfcfcd 0x03ff3fff8fff7ffb 0xbbfc38e3e3efcfcf

def z590 : W := mkw 0x61088a0c84422210 0x79e3249114c4c4c8 0xe000ff1f8fc70038 0xe78bb4101eeec0c0

def z591 : W := mkw 0x2148890886421210 0x79e32493144cc88c 0xe3f8c0000fc70003 0xfcabb4d39c0ec00c

def z592 : W := mkw 0x6c0166b530096969 0x0bc0000013b0a7fa 0x00003ffffe3fffff 0x03f0000003f1ffff

def z593 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000fc7e3f8000 0x038000000111f000

def z594 : W := mkw 0x000030d008000000 0x820cd80003330000 0x00003ffffff80000 0xe38ff80003ff0000

def z595 : W := mkw 0x8481400010090049 0x0000020848002022 0x0007000000388000 0x00100b0060013003

def z596 : W := mkw 0x0240010002001000 0x800c1862a0080804 0x03ff3f000fc07e03 0xbaec38e3e20e0e0c

def z597 : W := mkw 0x2401400010090049 0x09c000001000a0aa 0x000000fc7e3ff1ff 0xe3f44f000111f1ff

def z598 : W := mkw 0x635a9f6c8ed27692 0xfbef3cf3b7cfcfcd 0xe3f8ff1f8fc77e3b 0xffebb4d39eeececc

def z599 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0xffffc0fc700071fc 0xff4ffffffd1001f0

def z600 : W := mkw 0x2148890886421210 0x29e12403144cc88c 0x03f8ff1f8fc70003 0xefabb4039eeec00c

def z601 : W := mkw 0x025215600a905482 0x820c1862a30b0b05 0x03ff00e000387fc3 0x187408e3e1010f0f

def z602 : W := mkw 0xa6d351401a9914cb 0x09c01a0af80ba8af 0x03ffc0000fff8003 0x2cb03f03fc0ff00f

def z603 : W := mkw 0x0000184a4d240000 0x20013d0000475000 0x00003f1f8fff8000 0xe38bbf0002eff000

def z604 : W := mkw 0xa481442010094049 0x8bcc02685b00a3aa 0xffc7fffc7e3fffff 0xfffc4ffc7f11ffff

def z605 : W := mkw 0x0212146008904482 0x820c1860a3030301 0x03ff00e0003801c0 0xb81c38e3e1010103

def z606 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000e00e380000 0xa284080001010000

def z607 : W := mkw 0x41488b0c86423210 0x7023249304cc4c44 0xe0383f1f81c07e38 0xd34bb0d382ee0ec0

def z608 : W := mkw 0x0000080a45240000 0x2001250000445000 0x0000000000078000 0x000007000000f000

def z609 : W := mkw 0x000038da4d240000 0xa20dfd0003775000 0x00003f0381c00000 0xe00fff0002ee0000

def z610 : W := mkw 0x92a4000000000000 0x0400026ce8000000 0x1c07000000000000 0x0000002c60000000

def z611 : W := mkw 0x6148830482423210 0x59e2009314888ccc 0xe3f8c01c0e077e3b 0xffe004d39c00cecc

def z612 : W := mkw 0xa481400010090049 0x09c002085800a0aa 0x03c7c0e00e3ff1c3 0xbef40f207d01f10f

def z613 : W := mkw 0x025215600a905482 0xa20dfd62a30b0b05 0x03ff3fe00ff87fc3 0xfaffffe3e30f0f0f

def z614 : W := mkw 0x615a9f6c8ed27692 0x7be3249317cfcfcd 0xe3f8ffff8fff7ffb 0xfffbb4d39fefcfcf

def z615 : W := mkw 0xa481400010090049 0x09c002085800a0aa 0xe3c7c01c0e3ff03b 0xfff00f107c01f0cf

def z616 : W := mkw 0x82d215600a905482 0x820c1a6aeb0b0b05 0xffffffe00ff87fc3 0xfefc7fffff0f0f0f

def z617 : W := mkw 0x48003eff6d246920 0xf20ffdf403f75750 0x00003f0381c00e00 0x000bb0c002ee0e00

def z618 : W := mkw 0x6148bbdecf663210 0x7be3249317ffdccc 0xe3f8fffffffffe3b 0xffebb4d39ffffecc

def z619 : W := mkw 0xf1ec8b0c86423210 0x7de3e79f5ccccccc 0xfff8ff1f8fc77e3b 0xffebf7df9eeececc

def z620 : W := mkw 0x41488b0c86423210 0x7023249304cc4c44 0x03f83f038fc07e03 0xbaebb0c382ee0e0c

def z621 : W := mkw 0x4a523fff6fb47da2 0xf20ffdf6a3ff5f55 0xffff3fffffffffff 0xfbffffffe3ffffff

def z622 : W := mkw 0x0000209241240000 0x0000c10000301000 0x0000000070008000 0x0000430000103000

def z623 : W := mkw 0x480026b520006920 0x5202009003b00750 0xe0003ffff0007ffc 0xd34b80d003f00ff0

def z624 : W := mkw 0x0000000000000000 0x0000000000000000 0xfc000000000071fc 0x1040003c000001f0

def z625 : W := mkw 0x480026b520006920 0xd20ec0f403b00750 0x00003ffff0000e00 0xc30fc0c003f00e00

def z626 : W := mkw 0x0000000000000000 0x0000000000000000 0x03c700fc7e3ff1c3 0xfbf44f206111f10f

def z627 : W := mkw 0x635a8f2c86d27692 0x79e324f3b4cccfcd 0xe3ffff1f8fc77ffb 0xfffbb4f3feeecfcf

def z628 : W := mkw 0x40000a0c04002000 0x7003249000c44440 0xe0003f1f8fc77e38 0xf3cbb4d002eecec0

def z629 : W := mkw 0xe5c9cb0c964b3259 0x79e3269b5cccecee 0xe3ffff1f8ffffe3b 0xfffbbfd3feeffecf

def z630 : W := mkw 0xec81462530096969 0x59c202fc5880a7fa 0xffc7c00000007fff 0x1c7000fc7c000fff

def z631 : W := mkw 0x86935460189944cb 0x820c1a68eb032323 0x1c0700e0703881c4 0x00144b2c61113133

def z632 : W := mkw 0x6948afbda6427b30 0x7be3249317fccfdc 0xe3f8ffffffc77fff 0xffebb4d39ffecffc

def z633 : W := mkw 0x1324000000000000 0xf40ffdf5a4000000 0xfc38000000000000 0xd00ff0ff80000000

def z634 : W := mkw 0xb3ec890886421210 0x2de13f0bfc4cc88c 0x03ffc0000fc70003 0x2ca03f03fc0ec00c

def z635 : W := mkw 0x0200000000000000 0x800c1860a0000000 0x03ff00e00e3871c3 0xbafc38e3e101010f

def z636 : W := mkw 0x0000289a45240000 0x2001e50000745000 0x0000000380000000 0x0003800000e00000

def z637 : W := mkw 0x90a4000000000000 0x0400c30c48000000 0x1c00000000000000 0x0000430c00000000

def z638 : W := mkw 0x0000042000004000 0x820c006003000300 0x03c73fe00e387fc3 0xbafc08e063010f0f

def z639 : W := mkw 0x0000000000000000 0x820c000003000000 0x00003fe000000000 0x820c000003000000

def z640 : W := mkw 0x2000000000000000 0x09c0000010008088 0xffc0c0fc7e0771ff 0xffe4443c1d10c1fc

def z641 : W := mkw 0x235a9d688ed25692 0xabed3c63b74fcb8d 0x03ffffe00fff7fc3 0xbefc3ce3ff0fcf0f

def z642 : W := mkw 0x132438da4d240000 0xf60ffdf5a7775000 0x00383fffffff8000 0xe38fffc383fff000

def z643 : W := mkw 0x0000209000000000 0x0000c00000300000 0x0000001ff0000000 0x4103c00000f00000

def z644 : W := mkw 0x000038da4d240000 0xa20dfd0003775000 0x000000fff03f8000 0x4107cf0001f1f000

def z645 : W := mkw 0xec8166b530096969 0xdbcec2fc5bb0a7fa 0xfc00fffff007fffc 0xd74fc7fc1ff0fff0

def z646 : W := mkw 0xa481400010090049 0x09c002085800a0aa 0x03c7c0fc7e3f8003 0xefb44f007d11f00f

def z647 : W := mkw 0x6b5abffdaed27fb2 0xfbeffcf7b7ffcfdd 0xffffffffffff7fff 0xfffffcffffffcfff

def z648 : W := mkw 0x0000000000000000 0x0000000000000000 0x00003f0000007e00 0x924800c002000e00

def z649 : W := mkw 0x240178da5d2d0049 0xabcdfd001377f0aa 0x00003ffffffff1ff 0xe3ffff0003fff1ff

def z650 : W := mkw 0x6108badecd662210 0xfbeffd9117f7d4c8 0xe000ffffffff8038 0xe78fff101ffff0c0

def z651 : W := mkw 0x60488b0c86423210 0x09e0000210cccccc 0x03f83f1f8fc77e3b 0xbbe830c382eececc

def z652 : W := mkw 0x8080000000000000 0xd00ec2fc48000000 0xffc7c00000000000 0xfc0fcffc7c000000

def z653 : W := mkw 0x6148830482423210 0x59e2009314888ccc 0xe3f8ff1f80007e3b 0xdf6b80d39ee00ecc

def z654 : W := mkw 0x6108aa9ec5662210 0x79e3e59114f4d4c8 0xe000c01ff0078038 0x4503c7101cf0f0c0

def z655 : W := mkw 0xa481400010090049 0x09c002085800a0aa 0xffc0c01c7e07f03f 0xffe0471c1c10f0fc

def z656 : W := mkw 0x480026b520006920 0xd20ec0f403b00750 0xfc0000e070007ffc 0x104440fc01100ff0

def z657 : W := mkw 0x0040010002001000 0x0000000200080804 0x00383f0001c00e00 0x000830c3820e0e00

def z658 : W := mkw 0x480026b520006920 0x0200000003b00750 0x00003f0380000e00 0x0000000002e00e00

def z659 : W := mkw 0xec81629530092969 0x59c2c29c58b0a4fa 0xffc7c0fffe3ff1ff 0xfff7cf3c7df1f1ff

def z660 : W := mkw 0x0148890886421210 0x20212403044c4804 0x0038000001c00000 0x00003003800e0000

def z661 : W := mkw 0x0000000000000000 0xd00ec0f400000000 0xfc0000fc700071fc 0xd34fc0fc011001f0

def z662 : W := mkw 0x8481400010090049 0x0000020848002022 0x1c070000000001c4 0x0010002c60000133

def z663 : W := mkw 0x0000289a45240000 0xa00dfd0000745000 0x0000001ff0078000 0xe10fff0000f0f000

def z664 : W := mkw 0x2000000000000000 0x09c0000010008088 0xe3c0c0000000703b 0x1c6000101c0000cc

def z665 : W := mkw 0x080024b120004920 0x820cc06403300310 0x1c003fe070007fc4 0x924c40ec03100f30

def z666 : W := mkw 0xb5a5400010090049 0x7dc3e79d5c00a0aa 0xffc7c0fc7e3ff1ff 0xfff7cf3c7d11f1ff

def z667 : W := mkw 0x021234f249b44482 0x820cd960a3331301 0x000700e0703881c0 0x00144b2061113103

def z668 : W := mkw 0x91a4000000000000 0x5402029d4c000000 0xfc00c00000000000 0x0400001c1c000000

def z669 : W := mkw 0x93e4010002001000 0xf40fffffec080804 0xffffff000fc07e03 0xfeeffffffe0e0e0c

def z670 : W := mkw 0x2100000000000000 0x79c3249114008088 0xe3f8c01c0e07703b 0xffebb4d39c00c0cc

def z671 : W := mkw 0xb7a5400010090049 0xfdcffffdfc00a0aa 0xffffc000000071ff 0xfc7ffffffc0001ff

def z672 : W := mkw 0x61088a0c84422210 0x79e3249114c4c4c8 0xe3c0c01f8e07703b 0xffe384101ce0c0cc

def z673 : W := mkw 0x4000020400002000 0x5002009000800440 0x00003f0380000e00 0x000b80c002e00e00

def z674 : W := mkw 0x69488725a2427b30 0x59e200f714888fdc 0xfff8c00000007fff 0x1c6000ff9c000ffc

def z675 : W := mkw 0x0000104008000000 0xa20dfd0003030000 0x00003fe00ff80000 0xe28fff00030f0000

def z676 : W := mkw 0x4948afbda6427b30 0xf22fe4f707fc4f54 0xfc383ffff1c07ffc 0xd34ff0ff83fe0ff0

def z677 : W := mkw 0x004011400a001000 0x820c1802030b0804 0x03f83fe00ff87e03 0xbaec38c3830f0e0c

def z678 : W := mkw 0xa481400010090049 0x09c002085800a0aa 0xffc7c000000071ff 0xfc744f3c7c0001ff

def z679 : W := mkw 0x025211400a901482 0x00001802a00b0805 0x0038000001c00000 0x00003003800e0000

def z680 : W := mkw 0x080024b120004920 0x820cc06403300310 0xfc0000fc700071fc 0xd344403c011001f0

def z681 : W := mkw 0x0212146008904482 0x820c1860a3030301 0x00073fe00ff801c0 0xa29c3820630f0103

def z682 : W := mkw 0x137615600a905482 0xf60ffdf7a70b0b05 0x00383f0001c00e00 0x000bb0c3820e0e00

def z683 : W := mkw 0x2148b9dacf661210 0xabedfd03177fd88c 0x03f8ffffffff8003 0xefafff039ffff00c

def z684 : W := mkw 0x0000042000004000 0x820c006003000300 0x000000e0000001c0 0x0004002001000100

def z685 : W := mkw 0x4000020400002000 0x5002009000800440 0xe000001f80000038 0x4103801000e000c0

def z686 : W := mkw 0xf3ac8a0c84422210 0xfdeffffdfcc4c4c8 0xffffc01f80070038 0xfd0ffffffce0c0c0

def z687 : W := mkw 0x2000000000000000 0x09c0000010008088 0x0000001c0e07703b 0x03e000000000c0cc

def z688 : W := mkw 0x0040010002001000 0x0000000200080804 0x03f8000000007e03 0x186000c380000e0c

def z689 : W := mkw 0xe1c88b0c86423210 0x79e3269b5ccccccc 0xffffff1f8fc77e3b 0xffeffffffeeececc

def z690 : W := mkw 0x0212042000904482 0x00000060a0000301 0x00070000000001c0 0x0010002060000103

def z691 : W := mkw 0xb7f755601a9954cb 0xffcfffffff0babaf 0xfffffffc7fffffff 0xffffffffff1fffff

def z692 : W := mkw 0x0000042000004000 0x0000006000000300 0x0000000000007fc0 0x104000e000000f00

def z693 : W := mkw 0xa48178da5d2d0049 0x0bc002085b77f0aa 0xffc7fffffffff1ff 0xfff44f3c7ffff1ff

def z694 : W := mkw 0xa080000000000000 0x09c0020858008088 0xffc7c01c0e07703b 0xffe44f3c7c00c0cc

def z695 : W := mkw 0x2040010002001000 0x09c000021008888c 0xe3f8ff1c0fc77e3b 0xffe834d39e0ececc

def z696 : W := mkw 0xa481689a552d0049 0x29c1e7085874f0aa 0xffc7c0fffe3ff1ff 0xfff7cf3c7df1f1ff

def z697 : W := mkw 0x0000000000000000 0x800cc00000000000 0x0000000000000000 0xc00fc00000000000

def z698 : W := mkw 0x0000000000000000 0xd00ec0f400000000 0x0000000000000000 0x000b80c000000000

def z699 : W := mkw 0x8080000000000000 0xa00dff0848000000 0xffc7c00000000000 0xfc0fff3c7c000000

def z700 : W := mkw 0x2000000000000000 0x09c0000010008088 0xe3c7c0fc0e3f71fb 0xfff40c307d01c1cf

def z701 : W := mkw 0x005215600a905482 0x02000002030b0b05 0x03f83fe00ff87fc3 0xbaf830c3830f0f0f

def z702 : W := mkw 0x0212146008904482 0x820c1860a3030301 0x03c700e00e3871c3 0xbaf408206101010f

def z703 : W := mkw 0x6148830482423210 0x79e3249314888ccc 0xe3f8c00000007e3b 0xfc6bb4d39c000ecc

def z704 : W := mkw 0x480026b520006920 0xd20ec0f403b00750 0xe0003f1f80007e38 0xd34b80d002e00ec0

def z705 : W := mkw 0x0252052002905482 0x820c0062a3080b05 0x03ff3fe000007fc3 0x9a7c00e3e3000f0f

def z706 : W := mkw 0x8481400010090049 0x0000020848002022 0x1c00000070008004 0x0000430c00103030

def z707 : W := mkw 0xd3a40a0c04002000 0xf40ffffdecc44440 0xffffff1f8fc77e38 0xffcffffffeeecec0

def z708 : W := mkw 0x0100289804000000 0xf20fe4f507744000 0xfff8ffffffc70000 0xff8ff4ff9ffec000

def z709 : W := mkw 0x93a4000000000000 0x7403e7fdec000000 0xffffc00000000000 0xfc0bf7fffc000000

def z710 : W := mkw 0x92a4000000000000 0x840cdb6ce8000000 0xffffc00000000000 0xfc0c7ffffc000000

def z711 : W := mkw 0x91a4000000000000 0x7403e79d4c000000 0xfff8c00000000000 0x5c03c7df9c000000

def z712 : W := mkw 0x0100000000000000 0x7003249104000000 0xe3f8c0000e007003 0xfeebb4d39c00000c

def z713 : W := mkw 0x685abffdaed27fb2 0x0be0000213ffcfdd 0x00003fffffff7fff 0x03f0000003ffcfff

def z714 : W := mkw 0x93a4000000000000 0xd40e1afdec000000 0xffffc00000000000 0x1c0408fffc000000

def z715 : W := mkw 0x8280042000004000 0x820c1a68eb000300 0xfffffffc70007ffc 0xff4c7fffff100ff0

def z716 : W := mkw 0x1324000000000000 0xf40ffdf5a4000000 0xfff8c00000000000 0xfc0ff4ff9c000000

def z717 : W := mkw 0x93a4000000000000 0xa40dff69ec000000 0x03ffc00000000000 0xfc0fffe3fc000000

def z718 : W := mkw 0x000038da4d240000 0xa20dfd0003775000 0x00003ffff1ff8000 0x410fff0003fff000

def z719 : W := mkw 0x2948adb9a6425b30 0xabede467177ccb9c 0x1ff8c0e07fc701c7 0x2ca4742f9d1ec13c

def z720 : W := mkw 0x9ba424b120004920 0xf60ffffdef300310 0xffffc00000000000 0xfc0ffffffc000000

def z721 : W := mkw 0xa6d355601a9954cb 0x8bcc1a6afb0babaf 0x1c073ffc7fffffff 0x03f44b2c631fffff

def z722 : W := mkw 0x818038da4d240000 0xf20fff994f775000 0xffffffffffff8000 0xff8ffffffffff000

def z723 : W := mkw 0x4a0026b520006920 0xd20ed8f4a3b00750 0xffff3ffffe387fff 0xfbfff8ffe3f10fff

def z724 : W := mkw 0x480026b520006920 0x5202c0f403b00750 0xfc003ffff0007ffc 0x5343c0fc03f00ff0

def z725 : W := mkw 0x93a4000000000000 0x04000269ec000000 0x03ffc00000000000 0x1c0000e3fc000000

def z726 : W := mkw 0x0100000000000000 0x700324f504000000 0xfff8c00000000000 0xfc0bb4ff9c000000

def z727 : W := mkw 0x2048b9dacf661210 0xabedfd02137fd88c 0x00003fffffff8003 0xe3afff0003fff00c

def z728 : W := mkw 0x0000080804000000 0x2001240000444000 0x00003f1f8fff8000 0xe38bbf0002eff000

def z729 : W := mkw 0x91a4000000000000 0x7403269d4c000000 0xfff8c00000000000 0xfc0bb4df9c000000

def z730 : W := mkw 0x93a4209000000000 0xf40ffffdec300000 0xffffc01ff0000000 0xfd0ffffffcf00000

def z731 : W := mkw 0x93a4000000000000 0x5402c3fdec000000 0xffffc00000000000 0x1c0043fffc000000

def z732 : W := mkw 0x0240010002001000 0x800c1862a0080804 0x03ff3fe00ff87fc3 0xbafc38e3e30f0f0f

def z733 : W := mkw 0xd3a4020400002000 0xf40ffffdec800440 0xfffffffff0007ffc 0xff4ffffffff00ff0

def z734 : W := mkw 0x1324000000000000 0xf40ffdf5a4000000 0xe3f8c00000000000 0x1c0bb0d39c000000

def z735 : W := mkw 0x000038da4d240000 0xa20dfd0003775000 0xffc73ffffffff1ff 0xfbffff3c63fff1ff

def z736 : W := mkw 0x8180000000000000 0x200126094c000000 0x03ffc00000000000 0x2c003f03fc000000

def z737 : W := mkw 0x0100289a45240000 0x7003e59104745000 0xe3f8c01ff0078000 0xfd0bf7d39cf0f000

def z738 : W := mkw 0xa5c9c908964b1259 0x29e1260b5c4ce8ae 0x03ffc0000fc70003 0x2cb03403fc0ec00f

def z739 : W := mkw 0x4a5233d52a903da2 0x5002d896a0bb0c55 0xffff001ffff8003f 0x69b3f81fe0ff00ff

def z740 : W := mkw 0x91a4000000000000 0xf40fff9d4c000000 0xfff8c00000000000 0xfc0fffdf9c000000

def z741 : W := mkw 0xa481400010090049 0x09c002085800a0aa 0xffffc0fc7e3ff1ff 0xfffc7ffffd11f1ff

def z742 : W := mkw 0x93a4000000000000 0x540202fdec000000 0xffffc00000000000 0xbc0830fffc000000

def z743 : W := mkw 0xdba4062520006920 0xd60e1afdef800750 0xffffffe000007ffc 0xbe4c38ffff000ff0

def z744 : W := mkw 0xd3a4229400002000 0xf60ffffdefb00440 0xfffffffff0007e38 0xff4ffffffff00ec0

def z745 : W := mkw 0x91a4000000000000 0x5402029d4c000000 0xfff8c00000000000 0x1c0000df9c000000

def z746 : W := mkw 0x025211400a901482 0x00001802a00b0805 0x03ff3f000ff80e03 0x28b838c3e20f0e0f

def z747 : W := mkw 0x60488b0c86423210 0x09e0000210cccccc 0x00003f1f8fc77e3b 0xc3eb800002eececc

def z748 : W := mkw 0xa481400010090049 0x09c002085800a0aa 0xfc07c0fc7e3ff1ff 0x47f44f3c7d11f1ff

def z749 : W := mkw 0x93a4000000000000 0x840c1a69ec000000 0x03ffc00000000000 0xbc0c38e3fc000000

def z750 : W := mkw 0x9ba43cfb6d244920 0xf60ffffdef775310 0xffffffffffff81c4 0xff8ffffffffff130

def z751 : W := mkw 0x4b0026b520006920 0xf20ffcf5a7b00750 0xfffffffff0007ffc 0xff4ffcfffff00ff0

def z752 : W := mkw 0x93a4209000000000 0xa60dff09ef300000 0x03fffffff0000000 0xef0fff03fff00000

def z753 : W := mkw 0x93a4000000000000 0x24013f09ec000000 0x03ffc00000000000 0xec0bbf03fc000000

def z754 : W := mkw 0x6048bbdecf663210 0xabedfd0213ffdccc 0x00003f1f8fc77e3b 0x03ebb00002eececc

def z755 : W := mkw 0x00003cfa4d244000 0xa20dfd6003775300 0xfc003ffffffffffc 0xf3cffffc03fffff0

def z756 : W := mkw 0x490026b520006920 0x7203249107b00750 0xe3f8fffff0007ffc 0xff4bb4d39ff00ff0

def z757 : W := mkw 0x93a4000000000000 0xd40edbfdec000000 0xffffc00000000000 0xbc0c7bfffc000000

def z758 : W := mkw 0x93a4000000000000 0x7403ff9dec000000 0xffffc00000000000 0xfc0bffdffc000000

def z759 : W := mkw 0x025215600a905482 0x820c1862a30b0b05 0x03ff3ffc7ff87fff 0xbbfc38e3e31f0fff

def z760 : W := mkw 0x4900062520006920 0x500200f504800750 0xfff8c00000007ffc 0x1c4000ff9c000ff0

def z761 : W := mkw 0x93a4000000000000 0x74033ffdec000000 0xffffc00000000000 0xfc047ffffc000000

def z762 : W := mkw 0x93a4000000000000 0x24013f09ec000000 0xffffc00000000000 0x3c003f3ffc000000

def z763 : W := mkw 0x0100000000000000 0x7003249104000000 0xe3f8c00000000000 0x6c03b4139c000000

def z764 : W := mkw 0x025215600a905482 0x820c1862a30b0b05 0x03ff3f000ff87e03 0xbaf838c3e20f0e0f

def z765 : W := mkw 0x93a4000000000000 0xf40fe7fdec000000 0xffffc00000000000 0xdc0fc7fffc000000

def z766 : W := mkw 0x9bb634f128904da2 0xf60ffffdef330311 0xffffc0e0703801c4 0xfc1ffffffd110133

def z767 : W := mkw 0x93a4184a4d240000 0xa60d3f69ef475000 0x03ffffe00fff8000 0xbe8c3fe3ff0ff000

def z768 : W := mkw 0x93a4000000000000 0xa40dff6dec000000 0xffffc00000000000 0xfc047f3ffc000000

def z769 : W := mkw 0x025215600a905482 0x00001862a00b0b05 0x03ff3f000ff87fc3 0xbaf838e3e20f0f0f

def z770 : W := mkw 0x60488b0c86423210 0x09e0000210cccccc 0x00003f1f81c70e38 0x0100000002eecec0

def z771 : W := mkw 0x480026b520006920 0xd20ec0f403b00750 0xfc003ffff0007ffc 0x4347c03c03f00ff0

def z772 : W := mkw 0x93a4104008000000 0xa60d3f09ef030000 0x03ffffe00ff80000 0xae8c3f03ff0f0000

def z773 : W := mkw 0x93a4000000000000 0x04001b09ec000000 0x03ffc00000000000 0x0c000b03fc000000

def z774 : W := mkw 0x0100000000000000 0x7003249104000000 0xe3f8c00000000000 0xfc0fffd39c000000

def z775 : W := mkw 0xa7dbd9489edb16db 0x29e13e0bfc4fe8af 0x03ffc0000fff8003 0x2cb03f03fc0ff00f

def z776 : W := mkw 0x60488b0c86423210 0x09e0000210cccccc 0x03c73fff8fff7ffb 0xbbf4082063efcfcf

def z777 : W := mkw 0x0100000000000000 0x0000000104000000 0x03f8c00000000000 0x0c0000039c000000

def z778 : W := mkw 0x93b63cfa4db44482 0xf60ffffdef775301 0xffffffffffff81c0 0xff9ffffffffff103

def z779 : W := mkw 0x60488b0c86423210 0x09e0000210cccccc 0xe0003f1f8fc77e3b 0xd3e0001002eececc

def z780 : W := mkw 0xf2ec8b0c86423210 0x8decdb6ef8cccccc 0x1c073f1f8fc77e3b 0x03e44b2c62eececc

def z781 : W := mkw 0x025215600a905482 0x820c1862a30b0b05 0x03ff3fe00ff87fc3 0x2af838c3e30f0f0f

def z782 : W := mkw 0x000038da4d240000 0xa20de50003775000 0x00003fffffff8000 0xc38fc70003fff000

def z783 : W := mkw 0xdba426b520006920 0x7403e7fdecb00750 0xffffc01ff0007ffc 0x5d43c7fffcf00ff0

def z784 : W := mkw 0x61488b0c86423210 0x79e3249314cccccc 0xe3f8ffffffc77e3b 0xffeff4d39ffececc

def z785 : W := mkw 0x93a4000000000000 0x24012609ec000000 0x03ffc00000000000 0x2c003403fc000000

def z786 : W := mkw 0x91a4000000000000 0x7403e79d4c000000 0xffffc00000000000 0xfc0ffffffc000000

def z787 : W := mkw 0x605a872482d27692 0x09e0000210888fcd 0x0000000000007ffb 0x0070000000000fcf

def z788 : W := mkw 0x93a438da4d240000 0xf60ffffdef775000 0xffffffe3f1f88000 0xfc0fffffffff3000

def z789 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0xffffc0e0000071c0 0xfe4ffffffd000100

def z790 : W := mkw 0x93a4209241240000 0xf40ffffdec301000 0xffffc00070008000 0xfc0ffffffc103000

def z791 : W := mkw 0x4000020400002000 0x5002009000800440 0xfc003f1f80007ffc 0xd34b80fc02e00ff0

def z792 : W := mkw 0x6048830482423210 0x09e0000210888ccc 0x00003f000fc07e3b 0x02e00000020e0ecc

def z793 : W := mkw 0x93a4000000000000 0x74033ffdec000000 0xffffc00000000000 0x1c0030fffc000000

def z794 : W := mkw 0x605abffecff67692 0x0be0000213ffdfcd 0x00003ffffffffffb 0x03f0000003ffffcf

def z795 : W := mkw 0x60488b0c86423210 0x29e1240210cccccc 0x00003f1f8fc77e3b 0x43e3840002eececc

def z796 : W := mkw 0xdbb636f528906da2 0xf60ffffdefb30751 0xfffffffff0387ffc 0xff5ffffffff10ff3

def z797 : W := mkw 0x93a4104249240000 0x24013f09ec031000 0x03ffc00000388000 0x2c003f03fc013000

def z798 : W := mkw 0x0100000000000000 0x5002009104000000 0xe3f8c00000000000 0xdc0b80d39c000000

def z799 : W := mkw 0x245351401a9914cb 0x09c00002100ba8af 0x000000fc7ffff1ff 0x03f00000011ff1ff

def z800 : W := mkw 0x0000184a4d240000 0xa20d3d0003475000 0x00003fff8fff8000 0xe38fbf0003eff000

def z801 : W := mkw 0xdba4229520002920 0xf40ffffdecb00450 0xffffc0fff00071fc 0xff4ffffffdf001f0

def z802 : W := mkw 0x8180000000000000 0xf00fe6fd4c000000 0xffffc00000000000 0xfc0ffffffc000000

def z803 : W := mkw 0x0300000000000000 0x700324f1a4000000 0xe3ffc00000000000 0xfc0bb4f3fc000000

def z804 : W := mkw 0x480026b520006920 0x820cc06403b00750 0x1c003ffff0007ffc 0xc34fc02c03f00ff0

def z805 : W := mkw 0x245355601a9954cb 0x8bcc1802130babaf 0x00003ffc7fffffff 0xe3fc7f00031fffff

def z806 : W := mkw 0x2601400010090049 0x89cc1860b000a0aa 0x03ff00fc7e3ff1ff 0xbbfc38e3e111f1ff

def z807 : W := mkw 0x93a4000000000000 0x24013f09ec000000 0x0038c00000000000 0x040037039c000000

def z808 : W := mkw 0x6c49efbdb64b7b79 0xdbeec0f613fceffe 0xfc003fffffffffff 0xd3ffc0fc03ffffff

def z809 : W := mkw 0x1324000000000000 0xf40ffdf5a4000000 0xe038c00000000000 0x440bb4d39c000000

def z810 : W := mkw 0x000018480c000000 0xa20d3c0003474000 0x00003fffffff8000 0xe38fff0003fff000

def z811 : W := mkw 0x93a438da4d240000 0xf60ffffdef775000 0xffffc0e07fff8000 0xfc8ffffffd1ff000

def z812 : W := mkw 0x4100020400002000 0x7003249104800440 0xe3f8ff0380000e00 0xfc0bb4d39ee00e00

def z813 : W := mkw 0xdba426b520006920 0xf60ffffdefb00750 0x03ffff0380000e00 0x2c0bbfc3fee00e00

def z814 : W := mkw 0x6048830482423210 0x59e2009210888ccc 0xe000000000007e3b 0x106000d000000ecc

def z815 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0x03ffc00000000000 0xbc0fbfe3fc000000

def z816 : W := mkw 0x08003cfb6d244920 0xa20dfd0003775310 0x00003fffffff81c4 0xe38fff0003fff130

def z817 : W := mkw 0x490026b520006920 0xd20ec0f507b00750 0xfff8fffff0007ffc 0xdf4fc0ff9ff00ff0

def z818 : W := mkw 0xa48178da5d2d0049 0xabcdff085b77f0aa 0xffc7ff0381c071ff 0x1c7bb03c7eee01ff

def z819 : W := mkw 0x4a0026b520006920 0xd20ed8f4a3b00750 0xfc383ffff0007ffc 0xd34ff0ff83f00ff0

def z820 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0xffffc000000071fc 0xfc4ffffffc0001f0

def z821 : W := mkw 0xe589ca0c944b2259 0x79e326995cc4e4ea 0xfc00c01f8007003c 0x4503841c1ce0c0f0

def z822 : W := mkw 0x480026b520006920 0xd20ec0f403b00750 0xfc003fe380007ffc 0x924f80fc03e00ff0

def z823 : W := mkw 0x93a43cfa4d244000 0xf60ffffdef775300 0xffffffffffffffc0 0xffcfffffffffff00

def z824 : W := mkw 0x93a4000000000000 0x2401ff0dec000000 0x1fffc00000000000 0x2c007f0ffc000000

def z825 : W := mkw 0x61488b0c86423210 0x79e3249314cccccc 0xe3f8ff038fc70e03 0xfcabb4d39eeece0c

def z826 : W := mkw 0x6048bbdecf663210 0x0be0000213ffdccc 0x00003f1f8fc77e3b 0x03e0000002eececc

def z827 : W := mkw 0x93b6146008904482 0xa60d3f69ef030301 0x03ffc0e0003801c0 0x2c143f23fd010103

def z828 : W := mkw 0x60488b0c86423210 0x09e0000210cccccc 0x00003fff8fff7ffb 0x03f0000003efcfcf

def z829 : W := mkw 0x93a4000000000000 0x540202fdec000000 0xffffc000000071fc 0x1c4000fffc0001f0

def z830 : W := mkw 0x122438da4d240000 0xa60dfd64a3775000 0x00003fffffff8000 0xe38fff0003fff000

def z831 : W := mkw 0x0200000000000000 0x800c1860a0000000 0xe3ffc00000000000 0xfc0c3cf3fc000000

def z832 : W := mkw 0x92b634f249b44482 0x860cdb6ceb331301 0x1c0700e0703881c0 0x00144b2c61113103

def z833 : W := mkw 0x2148890886421210 0x29e12403144cc88c 0x03f8ff1f8fc77e03 0xffebb4c39eeece0c

def z834 : W := mkw 0x025215600a905482 0x820c1862a30b0b05 0x03ff00e00ff87fc3 0x38f438e3e10f0f0f

def z835 : W := mkw 0x245355601a9954cb 0x8bcc0062130babaf 0xfc003ffc7fffffff 0xd3fc40fc031fffff

def z836 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0xffffc0e0700001c4 0xfc0ffffffd100130

def z837 : W := mkw 0x605a9f6c8ed27692 0xdbee00f213cfcfcd 0xe0003fff8fff7ffb 0xd3ff80f003efcfcf

def z838 : W := mkw 0x4100229400002000 0xf20ffd9107b00440 0xe3f8fffff0007e38 0xff4fffd39ff00ec0

def z839 : W := mkw 0x000038da4d240000 0xa20dfd0003775000 0x00003ffffffff1c0 0xf3cfff2003fff100

def z840 : W := mkw 0x41488b0c86423210 0x7023249304cc4c44 0xe3f8ff038fc07e03 0xfeebb4d39eee0e0c

def z841 : W := mkw 0x480036f528006920 0xd20ec0f403b30750 0xfc003ffffff87ffc 0xd3cfc0fc03ff0ff0

def z842 : W := mkw 0x93a4000000000000 0xd40ec2fdec000000 0xffffc00000000000 0xfc0fcffffc000000

def z843 : W := mkw 0x2048890886421210 0x29e12402104cc88c 0x000000000fc70003 0x20a03400000ec00c

def z844 : W := mkw 0x93a4000000000000 0x24013f09ec000000 0x03ffc00000000000 0x0c003003fc000000

def z845 : W := mkw 0xdba426b520006920 0xf60ffffdefb00750 0xfffffffff0007ffc 0xdf4ff0fffff00ff0

def z846 : W := mkw 0xeed3472532997deb 0x59c202fef888afff 0xffffc00000007fff 0x1c7000fffc000fff

def z847 : W := mkw 0x000038da4d240000 0xa20dfd0003775000 0x00003fe38fff8000 0xa28fbf0003eff000

def z848 : W := mkw 0x000038da4d240000 0xa20dfd6403775000 0x1c003fffffff8000 0xe38fff2c03fff000

def z849 : W := mkw 0x00003cfa4d244000 0xa20dfd6003775300 0x03c73fffffffffc3 0xfbffffe063ffff0f

def z850 : W := mkw 0x4a1236f528906da2 0xd20ed8f4a3b30751 0xffc73ffffe387fff 0xfbffc8fc63f10fff

def z851 : W := mkw 0x93a4000000000000 0xa40d3f09ec000000 0x03ffc00000000000 0xac0c3f03fc000000

def z852 : W := mkw 0x2449c908964b1259 0x09e00002104ce8ae 0x000000000fff8003 0x00b00000000ff00f

def z853 : W := mkw 0x93a438da4d240000 0x560202fdef775000 0xffffffffffff8000 0x1f8000fffffff000

def z854 : W := mkw 0x480026b520006920 0x820cc00003b00750 0xfc003ffff0007ffc 0xd34fc03c03f00ff0

def z855 : W := mkw 0x480036f528006920 0xd20ed8f403b30750 0xfc003ffffffffffc 0xf3cffffc03fffff0

def z856 : W := mkw 0x0000000000000000 0x0000000000000000 0xe3f8c00000000000 0xfc0834d39c000000

def z857 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0xffffff000fc00000 0xfe8ffffffe0e0000

def z858 : W := mkw 0x0100080804000000 0x7003249104444000 0xe3f8ff0381c00000 0xfc0bb4d39eee0000

def z859 : W := mkw 0x61488b0c86423210 0x79e3249314cccccc 0xfff8ff1f8fc77e3b 0xffeff4ff9eeececc

def z860 : W := mkw 0x93a4104008000000 0xf60ffffdef030000 0xffffc0e000380000 0xfc0ffffffd010000

def z861 : W := mkw 0x480026b520006920 0xd20ec0f403b00750 0xfc003ffffe077ffc 0xf3cfc4fc03f0cff0

def z862 : W := mkw 0x000038da4d240000 0x2001fd0000775000 0x000000ffffff8000 0xe387ff0001fff000

def z863 : W := mkw 0x605a9f6c8ed27692 0x0be0000213cfcfcd 0x00003f1f8fc77e3b 0x03e0000002eececc

def z864 : W := mkw 0x4140030402003000 0x7003249304880c44 0xe3f8ff1f8fc07e3b 0xffebb4d39eee0ecc

def z865 : W := mkw 0x60488b0c86423210 0x79e3249210cccccc 0xe0003f1f8fc77e3b 0xf3ebb4d002eececc

def z866 : W := mkw 0x000038da4d240000 0x2201e50003775000 0x00003f1ff1c78000 0x4103c70002fef000

def z867 : W := mkw 0x480026b520006920 0x5002c0f400b00750 0xfc00001ff0000e3c 0x4103c0dc00f00ef0

def z868 : W := mkw 0x245355601a9954cb 0x0bc00002130babaf 0x00003fe00ff87fff 0x02f00000030f0fff

def z869 : W := mkw 0x480026b520006920 0xd20ec0f403b00750 0xfc003ffff0007ffc 0x134b80fc03f00ff0

def z870 : W := mkw 0x010038da4d240000 0xa20dfd0107775000 0x03f8ffffffff8000 0xef8fff039ffff000

def z871 : W := mkw 0x60489b4c8e423210 0x0be0000213cfcccc 0x00003fff8fff7e3b 0x03e0000003efcecc

def z872 : W := mkw 0x91f615600a905482 0x7603e79f4f0b0b05 0xfc00ffe00ff87fc3 0x46f3c71c1f0f0f0f

def z873 : W := mkw 0x93a438da4d240000 0xa60dff6def775000 0x1fffffffffff8000 0xef8fff2ffffff000

def z874 : W := mkw 0x025215600a905482 0x820c1862a30b0b05 0x03ff3fff8ff87fc3 0xfbffb8e3e3ef0f0f

def z875 : W := mkw 0x93a438da4d240000 0xa60dff6def775000 0x1fffc0e07fff8000 0x2c847f2ffd1ff000

def z876 : W := mkw 0xdba43eff6d246920 0xf60ffffdeff75750 0xfffffffff1c07ffc 0xff4ffffffffe0ff0

def z877 : W := mkw 0x93a4000000000000 0x54021afdec000000 0xffffc00000000000 0x3c0038fffc000000

def z878 : W := mkw 0x480026b520006920 0xd20ec0f403b00750 0xfc003ffff0007ffc 0x434bc0dc03f00ff0

def z879 : W := mkw 0xdba42a9f65242920 0xf40ffffdecf45450 0xffffc01ff007803c 0xfd0ffffffcf0f0f0

def z880 : W := mkw 0x480036f769246920 0xd20ec0f403b31750 0xfc003ffff038fffc 0xd34fc0fc03f13ff0

def z881 : W := mkw 0x93a4000000000000 0x7403e7fdec000000 0xfc38c00000000000 0x4403c7df9c000000

def z882 : W := mkw 0x93a4000000000000 0xd40ec2fdec000000 0xffffc00000000000 0x1c0b80fffc000000

def z883 : W := mkw 0xdba426b520006920 0xf60ffffdefb00750 0xffffffe3f0000fc4 0xfc0ffffffff00f30

def z884 : W := mkw 0xdba426b520006920 0xd60edbfdefb00750 0xffffc0e070007ffc 0x1c444bfffd100ff0

def z885 : W := mkw 0x41000a0c04002000 0x7003249104c44440 0xe3f8ff1f8fc77e38 0xffcbb4d39eeecec0

def z886 : W := mkw 0x0100000000000000 0xd00ec0f504000000 0xfff8c00000000000 0xdc0fc0ff9c000000

def z887 : W := mkw 0x93a4000000000000 0x740326fdec000000 0xffffc00000000000 0x5c0384fffc000000

def z888 : W := mkw 0x9ba424b120004920 0xa60dff6def300310 0x1fffc0e0700001c4 0x2c047f2ffd100130

def z889 : W := mkw 0x8180000000000000 0x500202994c000000 0xffffc00000000000 0x1c0000fffc000000

def z890 : W := mkw 0x0a5235f12a905da2 0x820cd866a33b0b15 0x1fff3ffffff87fc7 0xfbfff8efe3ff0f3f

def z891 : W := mkw 0x132438da4d240000 0xf60ffdf5a7775000 0xe3f8ff1f8fc70000 0xff8bb4d39eeec000

def z892 : W := mkw 0x6549cb0c964b3259 0x79e3249314ccecee 0xe3f8ff1f8fc77fff 0xfffbb4d39eeecfff

def z893 : W := mkw 0x93a438da4d240000 0xf60ffffdef775000 0xffffff1ff1c78000 0xfd0ffffffefef000

def z894 : W := mkw 0x4100020400002000 0x5002009104800440 0xe3f8c00000007e38 0x1c4000d39c000ec0

def z895 : W := mkw 0x69488b0da6423b30 0x79e3249714ccccdc 0xfff8ff1f8fc77e3f 0xffebb4df9eeecefc

def z896 : W := mkw 0x5a2426b520006920 0xd60ed9f4a3b00750 0xfc003ffff0007ffc 0xd34fc0fc03f00ff0

def z897 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0xffffc00000000000 0x5c07cffffc000000

def z898 : W := mkw 0xdba426b520006920 0xd60edafdefb00750 0xfffffffff0007ffc 0xff4ff8fffff00ff0

def z899 : W := mkw 0x93a4000000000000 0x24013f09ec000000 0x03ffc00000000000 0xec047f03fc000000

def z900 : W := mkw 0x2048890886421210 0x09e00002104cc88c 0x0000001c0fc7703b 0x03e00000000ec0cc

def z901 : W := mkw 0x4a1236f528906da2 0xd20ed8f4a3b30751 0xfc073ffffff87ffc 0xf3dff8fc63ff0ff3

def z902 : W := mkw 0x6848afbda6427b30 0xfbefe4f613fccfdc 0xfc003fffffc77fff 0xf3eff4fc03fecffc

def z903 : W := mkw 0x93a438da4d240000 0xf60ffffdef775000 0xffffffe38ff80000 0xfe8fffffffef0000

def z904 : W := mkw 0x6549cb0c964b3259 0x79e3249314ccecee 0xe3f8ff1f8ffffe3b 0xfffbb4d39eeffecf

def z905 : W := mkw 0xdba426b520006920 0xf60ffffdefb00750 0xffffff1ff0000e3c 0xfd0ffffffef00ef0

def z906 : W := mkw 0x025215600a905482 0x820c1862a30b0b05 0x1fff3fe07ff87fc7 0xbafc78efe31f0f3f

def z907 : W := mkw 0xa481400010090049 0x09c002085800a0aa 0xffc7fffc7e3fffff 0xfffc4ffc7f11ffff

def z908 : W := mkw 0xe5c9c304924b3259 0x59e2029b5c88acee 0xe3ffc00000007e3b 0x1c7000d3fc000ecf

def z909 : W := mkw 0x4800020520002920 0x5002009400800450 0xfc003f1f80007e3c 0xd34b80dc02e00ef0

def z910 : W := mkw 0x6048ab9ec7663210 0x09e0000210fcdccc 0x00003f1fffc7fe3b 0x03e0000002fefecc

def z911 : W := mkw 0x93a4000000000000 0xf40f3efdec000000 0xffffc00000000000 0xfc0fbcfffc000000

def z912 : W := mkw 0x480036f769246920 0xd20ed9f403b31750 0xfc003ffffff8fffc 0xf3cffbfc03ff3ff0

def z913 : W := mkw 0x490026b520006920 0xf20fe4f507b00750 0xe3f8ff0380000e00 0xfc0bb4d39ee00e00

def z914 : W := mkw 0x0100000000000000 0x7003249104000000 0xe3f8c00000000000 0x3c0034d39c000000

def z915 : W := mkw 0x000038da4d240000 0x2201e50003775000 0x00003fffffff8000 0xe38bf70003fff000

def z916 : W := mkw 0x93a4000000000000 0x24013f69ec000000 0x03ffc00000000000 0x3c003fe3fc000000

def z917 : W := mkw 0x000038da4d240000 0x820cd90003775000 0x00003fffffff8000 0xc38fcb0003fff000

def z918 : W := mkw 0x0100000000000000 0x7003249104000000 0x03f8c00000000000 0x2c0bb4c39c000000

def z919 : W := mkw 0xa481400010090049 0x09c002085800a0aa 0xffc7c0fc703ff1ff 0x5d744f3c7d11f1ff

def z920 : W := mkw 0x4a1236f769b46da2 0xd20ed9f4a3b31751 0xfc073ffff038fffc 0xd35fcbfc63f13ff3

def z921 : W := mkw 0x4800062520006920 0xd20e00f403800750 0xfc003fff80007ffc 0xd34f80fc03e00ff0

def z922 : W := mkw 0xdba4062520006920 0xf40ffffdec800750 0xffffff1f80007ffc 0xff4ffffffee00ff0

def z923 : W := mkw 0x93a4104008000000 0xf60ffffdef030000 0xffffffe00ff871c3 0xfeffffffff0f010f

def z924 : W := mkw 0x025215600a905482 0x820c1862a30b0b05 0xe3ff3ffc0ff87ffb 0xfbfc38f3e30f0fcf

def z925 : W := mkw 0x93a4289a45240000 0xf60ffffdef745000 0xfffffffff0078000 0xff0ffffffff0f000

def z926 : W := mkw 0x2441410012091049 0x09c000021008a8ae 0x00003ffc7fffffff 0x03f00000031fffff

def z927 : W := mkw 0x020038da4d240000 0xa20dfd60a3775000 0x00383fffffff8000 0xe38fffc383fff000

def z928 : W := mkw 0x025235f00a905482 0x820cd862a33b0b05 0xffff3ffffff87fff 0xfbfff8ffe3ff0fff

def z929 : W := mkw 0x0100000000000000 0x7003249104000000 0xe3ffc0e00e3871c3 0xfeffbcf3fd01010f

def z930 : W := mkw 0x0000289a45240000 0x2001e50000745000 0x0000001fffc78000 0x6183f70000fef000

def z931 : W := mkw 0xdba4062520006920 0xf60ffffdef800750 0xffffffe000007ffc 0xfe4fffffff000ff0

def z932 : W := mkw 0x48001e6f6d246920 0x70033df400c75750 0xfc0000000ffffffc 0x30c03ffc000ffff0

def z933 : W := mkw 0x93a430d249240000 0xd60edbfdef331000 0xffffc0e070388000 0x1c044bfffd113000

def z934 : W := mkw 0x0100080804000000 0x2001240104444000 0x03f8c0000fc70000 0x2c8034039c0ec000

def z935 : W := mkw 0x000038da4d240000 0xa20dfd0003775000 0x00003ffffffff1c3 0xe3ffff0003fff10f

def z936 : W := mkw 0xa6d355601a9954cb 0x8bcc1a6afb0babaf 0xfc38ff1c71c78e3c 0x450877df9e1efef0

def z937 : W := mkw 0x93a4000000000000 0x540202fdec000000 0xffffc00000000000 0x5c0047fffc000000

def z938 : W := mkw 0x0a5235f12a905da2 0x820cd866a33b0b15 0xffff3ffc7ff87fff 0xfbfc78ffe31f0fff

def z939 : W := mkw 0x2048994acf661210 0x09e00002104fd88c 0x000000000fff8003 0x00a00000000ff00c

def z940 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0x1fffc00000000000 0x2c0fffeffc000000

def z941 : W := mkw 0xdba426b520006920 0xf60ffffdefb00750 0xffffff0380007ffc 0xfc4ffffffee00ff0

def z942 : W := mkw 0x93a4000000000000 0xa40d3f69ec000000 0x03ffc00000000000 0x2c083fc3fc000000

def z943 : W := mkw 0x0140090806001000 0x70032493044c4804 0xe3f8ff1f8fc77e03 0xffebb4d39eeece0c

def z944 : W := mkw 0x93a438da4d240000 0xf60ffffdef775000 0xfffffffffffff1c3 0xfffffffffffff10f

def z945 : W := mkw 0x4a1236f528906da2 0xd20ed8f4a3b30751 0xfc003ffff0007ffc 0xd34fc0fc03f00ff0

def z946 : W := mkw 0x93a4080804000000 0xf40ffffdec444000 0xffffffffffff8000 0xff8ffffffffff000

def z947 : W := mkw 0x61488b0c86423210 0x79e3249314cccccc 0xe3f8ff038fc07e3b 0xbeebb0d39eee0ecc

def z948 : W := mkw 0x000038da4d240000 0xa20dfd0003775000 0x00003ffffffff1fc 0xe3cfff0003fff1f0

def z949 : W := mkw 0x93a438da4d240000 0xf40ffffdec775000 0xffffc01fffff8000 0xfd8ffffffcfff000

def z950 : W := mkw 0x61488b0c86423210 0x79e3249314cccccc 0xe3f8ff1f8ffffe3b 0xffebbfd39eeffecc

def z951 : W := mkw 0x0100000000000000 0x20013d0104000000 0x03f8c00000000000 0x2c003f039c000000

def z952 : W := mkw 0x4800229520002920 0x5002c09400b00450 0xfc003ffff0007ffc 0xd34fc0fc03f00ff0

def z953 : W := mkw 0x0100080804000000 0x7003249104444000 0xe3f8c01f80070000 0xfd0bb4d39ce0c000

def z954 : W := mkw 0x93a4000000000000 0xd40e02fdec000000 0xffffc00000000000 0x9c0c00fffc000000

def z955 : W := mkw 0x025211400a901482 0x800c1862a00b0805 0x03ff3f000ff87e03 0xbafc38e3e20f0e0f

def z956 : W := mkw 0x025215600a905482 0x820c1862a30b0b05 0xe3ffffe00ff87fc3 0xfefc3cf3ff0f0f0f

def z957 : W := mkw 0x0100000000000000 0x7003249104000000 0xe3f8ff1f80000000 0xff0bb4d39ee00000

def z958 : W := mkw 0xe7dbc72492db76db 0x59e202fbfc88afef 0xffffc00000007fff 0x1c7000fffc000fff

def z959 : W := mkw 0x93a4000000000000 0x74033f99ec000000 0xe3ffc00000000000 0x6c03bf13fc000000

def z960 : W := mkw 0x93a4000000000000 0xd40e1afdec000000 0xffffc00000000000 0xfc0c7ffffc000000

def z961 : W := mkw 0x6c5377f53a997deb 0x0bc0000213bbafff 0x00003fffffffffff 0x03f0000003ffffff

def z962 : W := mkw 0x97a5400010090049 0xf40ffffdec002022 0xffffc0e07e38f1c7 0xfefffffffd11313f

def z963 : W := mkw 0x93a4184a4d240000 0xf40ffffdec475000 0xffffc0fc7fff8000 0xff8ffffffd1ff000

def z964 : W := mkw 0xc5c9cb0c964b3259 0x7023269b4ccc6c66 0x1c3f3fe3f1f88fc4 0x001ffbefe3ff3f33

def z965 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0xffffc00000000000 0x5c0bf7fffc000000

def z966 : W := mkw 0x0100080804000000 0x7003249104444000 0xe3f8c0000fc70000 0xfc8bb4d39c0ec000

def z967 : W := mkw 0x9ba4042120004920 0xf40ffffdec000310 0xffffc000000001c4 0xfc0ffffffc000130

def z968 : W := mkw 0x0100000000000000 0x7003249104000000 0xe3f8ff000fc00000 0xfe8bb4d39e0e0000

def z969 : W := mkw 0x025215600a905482 0x820c1862a30b0b05 0x03ff3fe001c07fc3 0x9a7c30e3e30e0f0f

def z970 : W := mkw 0x93a4000000000000 0x24013f09ec000000 0x03ffc0000e3f8000 0x2c803f03fc01f000

def z971 : W := mkw 0x60488f2c86427210 0x8bec006213cccfcc 0x00003fff8fc77ffb 0x93ec00e003eecfcc

def z972 : W := mkw 0x93a438da4d240000 0xa60dff09ef775000 0x03ffff0381c00000 0x2c0bbf03feee0000

def z973 : W := mkw 0x025215600a905482 0x800c1862a00b0b05 0x03ff00000ff87fc3 0xb8fc38e3e00f0f0f

def z974 : W := mkw 0x025235f00a905482 0x820cd862a33b0b05 0x03ff3fe07ff87fc3 0xbafc78e3e31f0f0f

def z975 : W := mkw 0x93a430d008000000 0xf60ffffdef330000 0xfffffffffff80000 0xff8fffffffff0000

def z976 : W := mkw 0x93b6146008904482 0xf60ffffdef030301 0xffffffe000387fc0 0xfe5fffffff010f03

def z977 : W := mkw 0x93b6146008904482 0xf60ffffdef030301 0xffffc00000000000 0xfc0ffffffc000000

def z978 : W := mkw 0x0100080804000000 0x2001240104444000 0x03f8ff1f8fc70000 0xef8bb4039eeec000

def z979 : W := mkw 0xe589ca0c944b2259 0x79e326995cc4e4ea 0xe000c01f80078038 0x450387101ce0f0c0

def z980 : W := mkw 0x60488b0c86423210 0x09e0000210cccccc 0x0000001f80077e3b 0x0160000000e0cecc

def z981 : W := mkw 0x025215600a905482 0x820c1862a30b0b05 0x03ff3ffc7fffffc3 0xbbfc38e3e31fff0f

def z982 : W := mkw 0x0100000000000000 0x70033d9104000000 0xe3f8c00000000000 0xfc0bbfd39c000000

def z983 : W := mkw 0x93a4000000000000 0x74032699ec000000 0xe3ffc00000000000 0xfc0bb4d3fc000000

def z984 : W := mkw 0x4900062520006920 0x700324f504800750 0xfff8c00000007ffc 0xfc4bb4ff9c000ff0

def z985 : W := mkw 0x480026b520006920 0xd20ec0f403b00750 0xfff83ffff0007ffc 0xfb4ff0ff83f00ff0

def z986 : W := mkw 0x6848afbda6427b30 0xdbeec0f613fccfdc 0x00003f1f8fc77e3b 0x03eb80c002eececc

def z987 : W := mkw 0x61488b0c86423210 0x79e3249314cccccc 0xe038ff0381c00e38 0x040bb0d39eee0ec0

def z988 : W := mkw 0x6549cb0c964b3259 0x79e3249314ccecee 0xe3f8ffffffffffff 0xffffffd39fffffff

def z989 : W := mkw 0x000038da4d240000 0xa20dfd0003775000 0x03c03ffffffff003 0xfbefff0003fff00c

def z990 : W := mkw 0x93a438da4d240000 0xf60ffffdef775000 0xfffffffffffff1fc 0xffcffffffffff1f0

def z991 : W := mkw 0x4800229520002920 0x5002c09400b00450 0xfc003f1ff0007e3c 0x4343c01c02f00ef0

def z992 : W := mkw 0x93a4289a45240000 0xf40ffffdec745000 0xffffc0fffe3f8000 0xff8ffffffdf1f000

def z993 : W := mkw 0x0100000000000000 0x7003249104000000 0xe3f8ff0000007e00 0xfe4bb4d39e000e00

def z994 : W := mkw 0x93a4000000000000 0x540202fdec000000 0x03ffc00000000000 0x0c0000c3fc000000

def z995 : W := mkw 0xdba426b520006920 0xd60ec2fdefb00750 0xffffff0380000e00 0x1c0b80fffee00e00

def z996 : W := mkw 0x93a4000000000000 0xd40e1afdec000000 0xffffc00000000000 0x1c0830fffc000000

def z997 : W := mkw 0x93a4000000000000 0xf40fff99ec000000 0xe3ffc00000000000 0xfc0fffd3fc000000

def z998 : W := mkw 0x02003cfa4d244000 0xa20dfd60a3775300 0x03ff3fffffffffc0 0xfbcfffe3e3ffff00

def z999 : W := mkw 0x0000289a45240000 0x2001e50000745000 0x00003f1fffc78000 0x4383c70002fef000

def z1000 : W := mkw 0x93a438da4d240000 0xf60ffffdef775000 0xffffff1f8fc70000 0xff8ffffffeeec000

def z1001 : W := mkw 0x0300000000000000 0xd00e18f1a4000000 0xe3ffc00000000000 0xbc0c38f3fc000000

def z1002 : W := mkw 0x93a4000000000000 0x54020299ec000000 0xe3ffc00000000000 0x1c0000d3fc000000

def z1003 : W := mkw 0x0300000000000000 0xf00ffcf5a4000000 0xffffc00000000000 0xfc0ffcfffc000000

def z1004 : W := mkw 0x490026b520006920 0xf20ffdf507b00750 0xfff8fffff0007ffc 0xff4fffff9ff00ff0

def z1005 : W := mkw 0xdba426b520006920 0xf60ffffdefb00750 0xffffff0380007ffc 0x1c4bb0fffee00ff0

def z1006 : W := mkw 0x000038da4d240000 0xa20dfd0003775000 0x00003fffffff8000 0x4387cf0003fff000

def z1007 : W := mkw 0x0100000000000000 0x7003249104000000 0xfff8c00000000000 0xfc0ff4ff9c000000

def z1008 : W := mkw 0xdba426b520006920 0xf60ffffdefb00750 0xfc38fffff0007ffc 0xd74ff7ff9ff00ff0

def z1009 : W := mkw 0x000038da4d240000 0xa20dfd0003775000 0x00003fe3ffff8000 0x208fff0003fff000

def z1010 : W := mkw 0x1324000000000000 0x74033d91a4000000 0xe3f8c00000000000 0xfc0bb4d39c000000

def z1011 : W := mkw 0x02522dba47b45482 0x2001e562a07c5b05 0x03ff001ff007ffc3 0x5973c7e3e0f0ff0f

def z1012 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0xffffc0fc7e3ff1c3 0xfffffffffd11f10f

def z1013 : W := mkw 0x025215600a905482 0x820cd962a30b0b05 0x03ff3fe00ff87fc3 0xbafc7be3e30f0f0f

def z1014 : W := mkw 0xa5c9c908964b1259 0x29e1260b5c4ce8ae 0x03f8c0000fc78003 0x2ca037039c0ef00c

def z1015 : W := mkw 0x480026b520006920 0xd20ec0f403b00750 0xffc0fffff0007ffc 0xff4fc4fc1ff00ff0

def z1016 : W := mkw 0x000038da4d240000 0x2201240003775000 0x00003fffffff8000 0xe38fff0003fff000

def z1017 : W := mkw 0x91a4000000000000 0x7403e79d4c000000 0xfc38c00000000000 0x440bf7df9c000000

def z1018 : W := mkw 0x93a424b000004000 0xf60ffffdef300300 0xfffffffff0007fc0 0xff4ffffffff00f00

def z1019 : W := mkw 0xa481400010090049 0x09c002085800a0aa 0xffc7c0e07e3ff1ff 0x3cf44f3c7d11f1ff

def z1020 : W := mkw 0x68488725a2427b30 0x59e200f610888fdc 0xfc00000000007fff 0x106000fc00000ffc

def z1021 : W := mkw 0x61488b0c86423210 0x79e3249314cccccc 0xe3f8ff1f8fc77e3b 0x1febb0d39eeececc

def z1022 : W := mkw 0x6449cb0c964b3259 0x09e0000210ccecee 0x00003f1f8fc77fff 0x03f0000002eecfff

def z1023 : W := mkw 0x60488b0c86423210 0x09e0000210cccccc 0x00003f1f8fc77e3b 0xa3e8300002eececc

def z1024 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0xffffc0e0003801c0 0xfc1ffffffd010103

def z1025 : W := mkw 0xe5c9c304924b3259 0x59e2029b5c88acee 0xfff8c00000007e3f 0x1c6000df9c000efc

def z1026 : W := mkw 0xd3a4020400002000 0x74033f99ec800440 0xe3ffff1f80007e38 0xff4bbfd3fee00ec0

def z1027 : W := mkw 0x0100000000000000 0x5002009104000000 0xe3f8c00000000000 0xbc0830d39c000000

def z1028 : W := mkw 0x6148830482423210 0x59e2009314888ccc 0xe3f8ff1f8fc07e3b 0xffebb0d39eee0ecc

def z1029 : W := mkw 0x93a430d249240000 0xf60ffffdef331000 0xffffffe07ff88000 0xfe8fffffff1f3000

def z1030 : W := mkw 0x6848a7b5a2427b30 0x0be0000213b88fdc 0x00003ffff0007fff 0x0360000003f00ffc

def z1031 : W := mkw 0xdba426b520006920 0xf60ffffdefb00750 0xfffffffff0000e00 0xff0ffffffff00e00

def z1032 : W := mkw 0x61488b0c86423210 0x79e3249314cccccc 0x03f8ff038fc77e03 0xbeebb4c39eeece0c

def z1033 : W := mkw 0xd3a4020400002000 0x540202fdec800440 0xffffc00000007e38 0x1c4000fffc000ec0

def z1034 : W := mkw 0x93a4000000000000 0x540202fdec000000 0xffffc00000000000 0x3c000ffffc000000

def z1035 : W := mkw 0x49003eff6d246920 0xf20ffdf507f75750 0xfff8fffffffffffc 0xffcfffff9ffffff0

def z1036 : W := mkw 0xd9a426b520006920 0xf60fe7fd4fb00750 0xfff8fffff0007ffc 0xff4ff7ff9ff00ff0

def z1037 : W := mkw 0x480026b520006920 0xd20ec0f403b00750 0xffc73ffffe3fffff 0xfbffcffc63f1ffff

def z1038 : W := mkw 0x93a4000000000000 0xa40d3f69ec000000 0xffffc00000000000 0xfc0c7ffffc000000

def z1039 : W := mkw 0x0100000000000000 0x7003249104000000 0xe3f8c01c0e070000 0xff8bb4d39c00c000

def z1040 : W := mkw 0x93a4184a4d240000 0xf40ffffdec475000 0xffffff1f8fff8000 0xff8ffffffeeff000

def z1041 : W := mkw 0x0100000000000000 0xf00ffdf504000000 0xfff8c00000000000 0xfc0fffff9c000000

def z1042 : W := mkw 0x93a4000000000000 0xa40dff09ec000000 0x03ffc00000000000 0x2c047f03fc000000

def z1043 : W := mkw 0x93a4042000004000 0xf60ffffdef000300 0xfffffffc70007ffc 0xff4fffffff100ff0

def z1044 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0xfc38c00000000000 0xe40fffdf9c000000

def z1045 : W := mkw 0x8180000000000000 0x500202994c000000 0xffffc00000000000 0xfc044ffffc000000

def z1046 : W := mkw 0x60488b0c86423210 0x09e0000210cccccc 0x0000001f8fc7003b 0x01a0000000eec0cc

def z1047 : W := mkw 0xdba4229520002920 0x7403ff9decb00450 0xffffc01ff000003c 0x6d03ff1ffcf000f0

def z1048 : W := mkw 0x0300000000000000 0x20013c01a4000000 0x03ffc00000000000 0x2c003c03fc000000

def z1049 : W := mkw 0x4800229520002920 0xd00ec0f400b00450 0xfc003f1ff0007e3c 0xd34fc0fc02f00ef0

def z1050 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0xffffc00000000000 0x3c0bbffffc000000

def z1051 : W := mkw 0x93a4000000000000 0x540202fdec000000 0xfc38c00000000000 0x040000df9c000000

def z1052 : W := mkw 0x93a4000000000000 0x24013f09ec000000 0x03ffc0000e380003 0x2cb03f03fc01000f

def z1053 : W := mkw 0x3725400010090049 0xfdcffdf5b400a0aa 0x003800fc7e3ff1ff 0x03fbb0c38111f1ff

def z1054 : W := mkw 0xa481400010090049 0x09c002085800a0aa 0xffc7fffc7ffff1ff 0xfffc7f3c7f1ff1ff

def z1055 : W := mkw 0x97a5400010090049 0xf40ffffdec002022 0xffffc000000001c4 0xfc1ffffffc000133

def z1056 : W := mkw 0x025215600a905482 0x820c1862a30b0b05 0xffff3fe00ff87fc3 0xfafc78ffe30f0f0f

def z1057 : W := mkw 0x0000080804000000 0xa00dfd0000444000 0x00003fffffff8000 0xe38fff0003fff000

def z1058 : W := mkw 0x480026b520006920 0xd00ec0f400b00750 0xfc00001ff0007ffc 0xd14fc0fc00f00ff0

def z1059 : W := mkw 0x24537dfa5fbd54cb 0x0bc00002137ffbaf 0x00003fffffffffff 0x03f0000003ffffff

def z1060 : W := mkw 0xdba426b520006920 0xf60ffffdefb00750 0xffffffe380007fc0 0xfe4fffffffe00f00

def z1061 : W := mkw 0x60488b0c86423210 0x29e1240210cccccc 0x00003f1f8fc77e3b 0x23e0340002eececc

def z1062 : W := mkw 0x68488f2da6427b30 0x09e0000210cccfdc 0x00003f1f8fc77fff 0x03e0000002eecffc

def z1063 : W := mkw 0x41488b0c86423210 0x7023249304cc4c44 0xe3f8ff1f8fc70e00 0xff8bb4d39eeece00

def z1064 : W := mkw 0x97a5400010090049 0x540202fdec002022 0xffffc000000001c4 0x1c1000fffc000133

def z1065 : W := mkw 0x0100000000000000 0x7003e49504000000 0xfff8c00000000000 0xfc0bf4df9c000000

def z1066 : W := mkw 0xdba4020520002920 0xf40ffffdec800450 0xffffc0000000003c 0xfc0ffffffc0000f0

def z1067 : W := mkw 0x41488b0c86423210 0x7023249304cc4c44 0xe3f8ff0381c00e00 0x1c0bb0d39eee0e00

def z1068 : W := mkw 0x8180000000000000 0x700326994c000000 0xffffc00000000000 0xfc0bb4fffc000000

def z1069 : W := mkw 0x480026b520006920 0x5202009003b00750 0xfc003ffff0007ffc 0xd34fc0fc03f00ff0

def z1070 : W := mkw 0x025215600a905482 0x00001862a00b0b05 0x03ff00e00ff87fc3 0xbaf438e3e10f0f0f

def z1071 : W := mkw 0x010030d249240000 0xf20ffd9107331000 0xe3f8c0e070388000 0xfc0fffd39d113000

def z1072 : W := mkw 0x60488b0c86423210 0xd9eec0f610cccccc 0xfc003f1f8fc77e3b 0xd3efc0fc02eececc

def z1073 : W := mkw 0x93a4080a45240000 0x24013f09ec445000 0x03ffc00000078000 0x2c003f03fc00f000

def z1074 : W := mkw 0x025215600a905482 0x00001862a00b0b05 0x03ff000001c07fc3 0x187030e3e00e0f0f

def z1075 : W := mkw 0x8180000000000000 0xf00fff994c000000 0xffffc00000000000 0xfc0ffffffc000000

def z1076 : W := mkw 0x0100000000000000 0x5002009104000000 0xe3f8c00000000000 0xfc0004d39c000000

def z1077 : W := mkw 0x61488b0c86423210 0x79e3249314cccccc 0xe3f8ffff8fff7ffb 0xfffbb4d39fefcfcf

def z1078 : W := mkw 0x480026b520006920 0xd20ec0f403b00750 0x1c003ffff0007ffc 0x034fc0ec03f00ff0

def z1079 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0xfc38c00000000000 0x040bb0df9c000000

def z1080 : W := mkw 0x24534520129954cb 0x09c000021008abaf 0x0000000000007fff 0x0070000000000fff

def z1081 : W := mkw 0xdba426b520006920 0xf60ffffdefb00750 0xffffff1f80007e38 0xff4ffffffee00ec0

def z1082 : W := mkw 0x60488b0c86423210 0x09e0000210cccccc 0x00003f1f8fc77e3b 0x93e800c002eececc

def z1083 : W := mkw 0x60488b0c86423210 0x09e0000210cccccc 0x00003fffffc77fff 0x03e0000003fecffc

def z1084 : W := mkw 0x93a4000000000000 0x5402029dec000000 0xffffc00000000000 0x0c00001ffc000000

def z1085 : W := mkw 0x02123cfa4db44482 0xa20dfd60a3775301 0x00003fffffff8000 0xe38fff0003fff000

def z1086 : W := mkw 0x60488b0c86423210 0x09e0000210cccccc 0x00003ffffffffe3b 0x03e0000003fffecc

def z1087 : W := mkw 0x93a4000000000000 0x740327fdec000000 0xffffc00000000000 0x1c0007fffc000000

def z1088 : W := mkw 0x9ab634f128904da2 0x860cdb6ceb330311 0x1c0700e0703801c4 0x00144b2c61110133

def z1089 : W := mkw 0xdba426b520006920 0xd60edbfdefb00750 0xfffffffff0007ffc 0xdf4fcbfffff00ff0

def z1090 : W := mkw 0x93a4042000004000 0xa60d3f69ef000300 0x03ffffe000007fc0 0xbe4c3fe3ff000f00

def z1091 : W := mkw 0x9ba4042120004920 0x540202fdec000310 0xffffc000000001c4 0x1c0000fffc000130

def z1092 : W := mkw 0x000038da4d240000 0xa20dfd0003775000 0x00003f038fff8000 0xe08fff0002eff000

def z1093 : W := mkw 0x480026b520006920 0xd20ec0f403b00750 0xffc03ffffe007fff 0xfbefc0fc03f00ffc

def z1094 : W := mkw 0x4000229400002000 0xd20ec09003b00440 0xfc003ffff0007ffc 0xd34fc0fc03f00ff0

def z1095 : W := mkw 0x0252052002905482 0x00000062a0080b05 0x03ff00000fc07fc3 0x38f030e3e00e0f0f

def z1096 : W := mkw 0x93a4042000004000 0xf60ffffdef000300 0xffffff0000000e00 0xfc0ffffffe000e00

def z1097 : W := mkw 0x93a4000000000000 0x540202fdec000000 0xffffc00000000000 0xbc0408fffc000000

def z1098 : W := mkw 0x4100020400002000 0x7003249104800440 0xe3f8c01f80000038 0xfd0bb4d39ce000c0

def z1099 : W := mkw 0x93a4104008000000 0x24013f09ec030000 0x03ffc0000ff80000 0x2c803f03fc0f0000

def z1100 : W := mkw 0x000024b000004000 0x820cc06003300300 0xfc003ffff0007ffc 0xd34fc0fc03f00ff0

def z1101 : W := mkw 0x93a4000000000000 0x24013f09ec000000 0x03ffc00000000000 0xbc043f23fc000000

def z1102 : W := mkw 0x9ba434f369244920 0xf60ffffdef331310 0xffffc0e0703881c4 0xfc0ffffffd113130

def z1103 : W := mkw 0x685abffdaed27fb2 0xdbeec0f613ffcfdd 0xfc003fffffff7fff 0xd3ffc0fc03ffcfff

def z1104 : W := mkw 0x132438da4d240000 0xa60dfd01a7775000 0x00383fffffff8000 0xe38fff0383fff000

def z1105 : W := mkw 0x93b6042000904482 0xf40ffffdec000301 0xffffc000000001c0 0xfc1ffffffc000103

def z1106 : W := mkw 0x0100000000000000 0xf00f24f104000000 0xe3f8c00000000000 0xfc0fb4f39c000000

def z1107 : W := mkw 0x93a4000000000000 0xf40f3ffdec000000 0xffffc00000000000 0xbc0c3ffffc000000

def z1108 : W := mkw 0x480026b520006920 0xd20ec0f403b00750 0xfc003ffff007fffc 0xd34fc7fc03f0fff0

def z1109 : W := mkw 0x480036f769246920 0xd20ed9f403b31750 0xfc003ffff0007ffc 0xd34fc0fc03f00ff0

def z1110 : W := mkw 0x480026b520006920 0x5202c09403b00750 0xfc003ffff0007ffc 0xd347c03c03f00ff0

def z1111 : W := mkw 0x020038da4d240000 0xa20dfd00a3775000 0x03ff3fffffff8000 0xeb8fff03e3fff000

def z1112 : W := mkw 0x6449cb0c964b3259 0x29e1240210ccecee 0x00003fffffffffff 0xe3ffff0003ffffff

def z1113 : W := mkw 0x93a438da4d240000 0xf60fff9def775000 0xffffffffffff8000 0xef8fff1ffffff000

def z1114 : W := mkw 0x93a4000000000000 0x24013f09ec000000 0x03ffc00000000000 0xbc083fc3fc000000

def z1115 : W := mkw 0x93b6042000904482 0x540202fdec000301 0xffffc000000001c0 0x1c1000fffc000103

def z1116 : W := mkw 0x480026b520006920 0x5002c0f400b00750 0xfc00000380007ffc 0x104380fc00e00ff0

def z1117 : W := mkw 0x41488b0c86423210 0x7023249304cc4c44 0xe038ff0381c00e00 0x440bb4d39eee0e00

def z1118 : W := mkw 0x93a4000000000000 0x24013f09ec000000 0x03ffc0e00e3871c3 0xbef43f23fd01010f

def z1119 : W := mkw 0x41003ade4d242000 0xf20ffd9107f75440 0xe3f8fffffffffe38 0xffcfffd39ffffec0

def z1120 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0xffffc0fc7e3ff1fc 0xffcffffffd11f1f0

def z1121 : W := mkw 0x010038da4d240000 0xf20ffd9107775000 0xe3f8ff0381c00000 0xfc0bb4d39eee0000

def z1122 : W := mkw 0x631a9e6c8cd26692 0xfbef3cf1b7c7c7c9 0xe007c0ff803f01f8 0x45178c307de1c1c3

def z1123 : W := mkw 0x4a0036f528006920 0xd20ed8f4a3b30750 0xffff3ffffff87ffc 0xfbcff8ffe3ff0ff0

def z1124 : W := mkw 0x000038da4d240000 0x2001fd0000775000 0x0000001ff1c78000 0x4103f70000fef000

def z1125 : W := mkw 0x2040010002001000 0x09c000021008888c 0x00003f1c0fc77e3b 0x03e00000020ececc

def z1126 : W := mkw 0x480026b520006920 0xd20ec0f403b00750 0xfc003ffffe387ffc 0xf3cfc8fc03f10ff0

def z1127 : W := mkw 0x0100209000000000 0xf20fe49107300000 0xe3f8fffff0000000 0xff0ff4d39ff00000

def z1128 : W := mkw 0x6048830482423210 0x59e2009210888ccc 0xe0003f1f80007e3b 0xd36b80d002e00ecc

def z1129 : W := mkw 0x61488b0c86423210 0x79e3249314cccccc 0xe3f8ff0381c07e3b 0xfc6bb4d39eee0ecc

def z1130 : W := mkw 0x0252052002905482 0x820c0062a3080b05 0x03ff3fe00fc07fc3 0xbafc30e3e30e0f0f

def z1131 : W := mkw 0x000038da4d240000 0xa20dfd0003775000 0x00003fffffff8000 0x038ffb0003fff000

def z1132 : W := mkw 0xec8166b530096969 0xdbcec2fc5bb0a7fa 0x03c7ff038e3f8e03 0x2cbb8fc07ee1fe0f

def z1133 : W := mkw 0x000038da4d240000 0xa20dfd0003775000 0x03f83fffffff8000 0xfb8fffc383fff000

def z1134 : W := mkw 0x93a4104008000000 0xd60e1afdef030000 0xffffffe00ff80000 0xbe8c38ffff0f0000

def z1135 : W := mkw 0xdba4062520006920 0x540202fdec800750 0xffffc00000000e00 0x1c0000fffc000e00

def z1136 : W := mkw 0x480026b520006920 0xd20ec0f403b00750 0xfc003fffffc07ffc 0xf3cff0fc03fe0ff0

def z1137 : W := mkw 0x93a4209000000000 0xd60ec2fdef300000 0xfffffffff0000000 0xdf0fc0fffff00000

def z1138 : W := mkw 0x93a4000000000000 0x540202fdec000000 0xffffc00000000000 0xdc0b80fffc000000

def z1139 : W := mkw 0x828038da4d240000 0xa20dff68eb775000 0xffffffffffff8000 0xff8ffffffffff000

def z1140 : W := mkw 0x4a1226b520906da2 0xd20ec0f4a3b00751 0xfc073ffff0007ffc 0xd35fc0fc63f00ff3

def z1141 : W := mkw 0x93a4000000000000 0x74033f99ec000000 0xe3ffc00000000000 0x3c003fd3fc000000

def z1142 : W := mkw 0x93a4000000000000 0xd40edbfdec000000 0xffffc00000000000 0xdc0fcbfffc000000

def z1143 : W := mkw 0xdba4062520006920 0xf40ffffdec800750 0xffffc0fc70007ffc 0xff4ffffffd100ff0

def z1144 : W := mkw 0x0300000000000000 0xf00f3cf1a4000000 0xe3f8c00000000000 0xfc0bb4d39c000000

def z1145 : W := mkw 0x61488b0c86423210 0x79e3249314cccccc 0x03f8ff0381c00e03 0x0c2bb0c39eee0e0c

def z1146 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0xfc3fc00000000000 0x440ffffffc000000

def z1147 : W := mkw 0x000038da4d240000 0x2001e50000775000 0x0000001fffff8000 0x4183c70000fff000

def z1148 : W := mkw 0xdba426b520006920 0xf40ffffdecb00750 0xffffc01ff0007ffc 0xfd4ffffffcf00ff0

def z1149 : W := mkw 0x0100000000000000 0x2001240104000000 0x03f8c00000000000 0xec0bb4039c000000

def z1150 : W := mkw 0x8280000000000000 0x00001a08e8000000 0x03ffc00000000000 0x2c003f03fc000000

def z1151 : W := mkw 0x6449fbdedf6f3259 0xabedfd0213fffcee 0x00003fffffffffff 0xe3ffff0003ffffff

def z1152 : W := mkw 0x480026b761246920 0xd20ec1f403b01750 0xfc003ffff000fffc 0xd34fc3fc03f03ff0

def z1153 : W := mkw 0x93a4000000000000 0x540202fdec000000 0xffffc0fc7e3f8000 0xff844ffffd11f000

def z1154 : W := mkw 0x60488b0c86423210 0x09e0000210cccccc 0x00003f1f8fc77e3b 0xe3e0040002eececc

def z1155 : W := mkw 0x60488f2c86427210 0x0be0000213cccfcc 0x00003fff8fc77ffb 0x03e0000003eecfcc

def z1156 : W := mkw 0xdba426b520006920 0xf60ffffdefb00750 0xffffc0fff00001fc 0xfd0ffffffdf001f0

def z1157 : W := mkw 0x6449fbdedf6f3259 0x0be0000213fffcee 0x00003fffffffffff 0x03f0000003ffffff

def z1158 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0x0038c00000000000 0x040bb7c39c000000

def z1159 : W := mkw 0xdba426b520006920 0xf60ffffdefb00750 0xffffc0e070007ffc 0xfc4ffffffd100ff0

def z1160 : W := mkw 0x010038da4d240000 0xf20ffdf507775000 0xfff8ffffffff8000 0xff8fffff9ffff000

def z1161 : W := mkw 0xc98026b520006920 0xf20fe6fd4fb00750 0xfffffffff0007ffc 0xff4ffffffff00ff0

def z1162 : W := mkw 0x025215600a905482 0x820c1862a30b0b05 0x03ff3fe00fffffc3 0xbafc3fe3e30fff0f

def z1163 : W := mkw 0x97a5400010090049 0x540202fdec002022 0xffffc0e0703881c4 0x1c144bfffd113133

def z1164 : W := mkw 0xdba426b520006920 0x26013f09efb00750 0x03fffffff0007ffc 0x2f403f03fff00ff0

def z1165 : W := mkw 0x0100000000000000 0xf00fe4f504000000 0xe3f8c00000000000 0xfc0bb4d39c000000

def z1166 : W := mkw 0x000038da4d240000 0x2001fd0000775000 0x00003f1fffff8000 0xe38bff0002fff000

def z1167 : W := mkw 0x91a4000000000000 0x240127094c000000 0x03f8c00000000000 0x2c0037039c000000

def z1168 : W := mkw 0x02123cfa4db44482 0xa20dfd60a3775301 0x03ff3fffffff81c0 0xfb9fffe3e3fff103

def z1169 : W := mkw 0x4800062520006920 0x500200f400800750 0xfc003f0380007ffc 0x104b80fc02e00ff0

def z1170 : W := mkw 0x93a4104249240000 0xf40ffffdec031000 0xffffc00000388000 0xfc0ffffffc013000

def z1171 : W := mkw 0xdba4229520002920 0xf40ffffdecb00450 0xffffc00380000000 0xfc0ffffffce00000

def z1172 : W := mkw 0x000038da4d240000 0xa20dfd0003775000 0xfc003fffffff8000 0xf38fff3c03fff000

def z1173 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0xffffc0000e3f8000 0xfc8ffffffc01f000

def z1174 : W := mkw 0x6048bbdecf663210 0xdbeec09213ffdccc 0xe0003ffffffffe3b 0xd3efc0d003fffecc

def z1175 : W := mkw 0x605abffecff67692 0xabedfd0213ffdfcd 0x00003ffffffffffb 0xe3ffff0003ffffcf

def z1176 : W := mkw 0x480026b520006920 0xd20ec0f403b00750 0xfc003f1ff0000e3c 0xd10fc0fc02f00ef0

def z1177 : W := mkw 0x025215600a905482 0x820c1862a30b0b05 0x03ff3fe001f87fc3 0x187c38e3e30f0f0f

def z1178 : W := mkw 0xdba43adf6d242920 0xf60ffffdeff75450 0xffffffffffff803c 0xff8ffffffffff0f0

def z1179 : W := mkw 0x000038da4d240000 0x2201fd0003775000 0x00003fffffff8000 0x6383ff0003fff000

def z1180 : W := mkw 0x6148b3d6cb663210 0xdbeed99317bb9ccc 0xe3f8c0e07038fe3b 0x1c644bd39d113ecc

def z1181 : W := mkw 0x6048830482423210 0x09e0000210888ccc 0x0000001c0e077e3b 0x03e000000000cecc

def z1182 : W := mkw 0x61488b0c86423210 0x79e3249314cccccc 0xe3f8ff1f8fc70e3b 0x6dabb4d39eeececc

def z1183 : W := mkw 0x61488b0c86423210 0x79e3249314cccccc 0x0038ff0381c70e00 0x040bb4c39eeece00

def z1184 : W := mkw 0x93a430d249240000 0xa60dff09ef331000 0x03ffc0e070388000 0x2c047f03fd113000

def z1185 : W := mkw 0x61488b0c86423210 0x79e3249314cccccc 0xe3f8ff1f81c77e3b 0x5d6bb4d39eeececc

def z1186 : W := mkw 0x93a4000000000000 0xa40dff6dec000000 0x1fffc00000000000 0xec0fff2ffc000000

def z1187 : W := mkw 0x93a4042000004000 0xd60e02fdef000300 0xffffffe000007fc0 0x9e4c00ffff000f00

def z1188 : W := mkw 0x481236f528906da2 0xd20ec0f403b30751 0xfc003ffff0387ffc 0xd35fc0fc03f10ff3

def z1189 : W := mkw 0x93a4000000000000 0x0400026dec000000 0x1fffc00000000000 0x0c00002ffc000000

def z1190 : W := mkw 0xdba426b520006920 0xf60ffffdefb00750 0xfffffffffe3ffffc 0xffcffffffff1fff0

def z1191 : W := mkw 0x4800062520006920 0x500200f400800750 0xfc00001f80007ffc 0x514380fc00e00ff0

def z1192 : W := mkw 0x480026b520006920 0x5002c09400b00750 0xfc00001ff0007ffc 0x4143c01c00f00ff0

def z1193 : W := mkw 0x5b2426b520006920 0xd60ec0f5a7b00750 0xfc383ffff0007ffc 0xd34fc0ff83f00ff0

def z1194 : W := mkw 0x97a570d2592d0049 0xf60ffffdef333022 0xffffc0e0703881c4 0xfc1ffffffd113133

def z1195 : W := mkw 0x6848bfffef667b30 0xabedfd0213ffdfdc 0x00003fffffffffff 0xe3efff0003fffffc

def z1196 : W := mkw 0x0252052002905482 0x800c1862a0080b05 0x03ff3f000fc07fc3 0xbafc38e3e20e0f0f

def z1197 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0xffffc0000e007003 0xfeeffffffc00000c

def z1198 : W := mkw 0x6848bfffef667b30 0x0be0000213ffdfdc 0x00003fffffffffff 0x03e0000003fffffc

def z1199 : W := mkw 0x61488b0c86423210 0x79e3249314cccccc 0xe3f8ffff8fff7e3b 0xffefbcd39fefcecc

def z1200 : W := mkw 0x93a4289a45240000 0xf40ffffdec745000 0xffffff1fffc78000 0xff8ffffffefef000

def z1201 : W := mkw 0x6048bbdecf663210 0xfbeffd9213ffdccc 0xe0003ffffffffe3b 0xf3efffd003fffecc

def z1202 : W := mkw 0x005215600a905482 0x02000002030b0b05 0x03ff3fe00ff87fc3 0xbafc38e3e30f0f0f

def z1203 : W := mkw 0x93a4000000000000 0x840cdb6dec000000 0x1fffc00000000000 0x0c044b2ffc000000

def z1204 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0xffffc0fc7e3871ff 0xfffffffffd1101ff

def z1205 : W := mkw 0x6848afbda6427b30 0x8becc06613fccfdc 0x1c003fffffc77fff 0x03e4402c03fecffc

def z1206 : W := mkw 0x93a438da4d240000 0xf60ffffdef775000 0xfffffffff1c00000 0xff0ffffffffe0000

def z1207 : W := mkw 0xdba436f528006920 0xf60ffffdefb30750 0xfffffffffff87ffc 0xffcfffffffff0ff0

def z1208 : W := mkw 0xa481400010090049 0x09c002085800a0aa 0xffc7fffffe3ff1ff 0xffffcf3c7ff1f1ff

def z1209 : W := mkw 0x000038da4d240000 0xa20dfd0003775000 0x03c73fffffff8003 0xebbfff0063fff00f

def z1210 : W := mkw 0x61488b0ec7663210 0x79e3259314ccdccc 0xe3f8ff1f8fc7fe3b 0xffebb7d39eeefecc

def z1211 : W := mkw 0x93a4289804000000 0xf60ffffdef744000 0xffffffffffc70000 0xff8ffffffffec000

def z1212 : W := mkw 0x91a4000000000000 0x7403e79d4c000000 0xfff8c00000000000 0x6c03f71f9c000000

def z1213 : W := mkw 0x0000289a45240000 0xa20de50003745000 0x00003fffffc78000 0xe38ff70003fef000

def z1214 : W := mkw 0x0a5235f12a905da2 0x820c1862a33b0b15 0x03ff3fe07ff87fc7 0xbafc38e3e31f0f3f

def z1215 : W := mkw 0x93a4000000000000 0x24012709ec000000 0x03ffc00000000000 0x0c000703fc000000

def z1216 : W := mkw 0x025215600a905482 0x820c1862a30b0b05 0x03ff3ffc7ff87fc3 0xfbfc78e3e31f0f0f

def z1217 : W := mkw 0x1324000000000000 0xf40ffdf5a4000000 0xe3ffc00000000000 0xfc0fbcf3fc000000

def z1218 : W := mkw 0x41488b0c86423210 0x7023249304cc4c44 0xe3f8ff1f81c07e38 0xff4bb4d39eee0ec0

def z1219 : W := mkw 0x000038da4d240000 0x820cc00003775000 0x00003fffffff8000 0xe38fcf0003fff000

def z1220 : W := mkw 0x0040010002001000 0x0000000200080804 0x03ff3f000ff87e03 0xbaf838c3e20f0e0f

def z1221 : W := mkw 0x93a438da4d240000 0xf60ffffdef775000 0xfc38ff1ff1c78000 0x450bf7df9efef000

def z1222 : W := mkw 0x000038da4d240000 0xa20dfd0003775000 0x00073fffffff81c0 0xe39fff2063fff103

def z1223 : W := mkw 0x0000289a45240000 0x2001e50000745000 0x00003fffffff8000 0xe38fff0003fff000

def z1224 : W := mkw 0x1324000000000000 0xf40ffdf5a4000000 0x03f8c00000000000 0x2c0bb4c39c000000

def z1225 : W := mkw 0x61488b0c86423210 0x79e3249314cccccc 0xe3f8ffff8fc77ffb 0xffefb4f39feecfcc

def z1226 : W := mkw 0xd3a4020400002000 0x540202fdec800440 0xffffff1f80007e38 0xdf4b80fffee00ec0

def z1227 : W := mkw 0x000038da4d240000 0xa00dfd0000775000 0x0000001fffff8000 0xe18fff0000fff000

def z1228 : W := mkw 0xf5adca0c944b2259 0x7de3e79d5cc4e4ea 0xfc00c01ff007803c 0x4503c71c1cf0f0f0

def z1229 : W := mkw 0x480026b520006920 0xd20ec0f403b00750 0xfc003ffff038fffc 0xd34fcbfc03f13ff0

def z1230 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0xffffc00000000000 0x6c07ff3ffc000000

def z1231 : W := mkw 0x000038da4d240000 0xa20dfd0003775000 0x00003f1ff1c78000 0xe10fff0002fef000

def z1232 : W := mkw 0x93a4000000000000 0x2401ff09ec000000 0x03ffc00000000000 0x6c03ff03fc000000

def z1233 : W := mkw 0x24534520129954cb 0x09c000021008abaf 0x000000fc7e3fffff 0x03f000000111ffff

def z1234 : W := mkw 0x93a438da4d240000 0xf60ffffdef775000 0xffffff0381c00000 0x1c0bb0fffeee0000

def z1235 : W := mkw 0x93a4080804000000 0xf40ffffdec444000 0xffffc01f80070000 0xfd0ffffffce0c000

def z1236 : W := mkw 0xa5c9d94adf6f1259 0x29e13f0b5c4ff8ae 0x03ffc0000fff8003 0x2cb03f03fc0ff00f

def z1237 : W := mkw 0x025215600a905482 0x820c1862a30b0b05 0x03ff3fe00ff80fc3 0x28bc38e3e30f0f0f

def z1238 : W := mkw 0x61488b0c86423210 0x79e3249314cccccc 0x03f8ff1f8fc77e3b 0x2febb4c39eeececc

def z1239 : W := mkw 0x480026b520006920 0xd20ec0f403b00750 0xfc003f0380000e3c 0x000b80dc02e00ef0

def z1240 : W := mkw 0x480026b520006920 0xd20ec09403b00750 0xfc003ffff0007ffc 0xc34fc01c03f00ff0

def z1241 : W := mkw 0xdba426b520006920 0xf60fe6fdefb00750 0xfffffffff0007ffc 0xff4ff4fffff00ff0

def z1242 : W := mkw 0x93b6146008904482 0xd60e1afdef030301 0xffffc0e0003801c0 0x1c1408fffd010103

def z1243 : W := mkw 0x000038da4d240000 0xa20dfd0003775000 0x000000ffffff8000 0x6187ff0001fff000

def z1244 : W := mkw 0x02123cfa4db44482 0xa20dfd60a3775301 0x00073fffffffffc0 0xf3dfffe063ffff03

def z1245 : W := mkw 0x4a1236f528906da2 0xd20ed8f4a3b30751 0xffff3ffff0387ffc 0xfb5ff8ffe3f10ff3

def z1246 : W := mkw 0x6848a7b5a2427b30 0xdbeec0f613b88fdc 0xfc003ffff0007fff 0xd36fc0fc03f00ffc

def z1247 : W := mkw 0x205a99488ed21692 0x09e00002104fc88d 0x000000000fff0003 0x00b00000000fc00f

def z1248 : W := mkw 0x93a438da4d240000 0xf60ffffdef775000 0x03ffffffffff8000 0xef8fffc3fffff000

def z1249 : W := mkw 0x000038da4d240000 0xa20dfd0003775000 0x00003f0381c78000 0x000bb70002eef000

def z1250 : W := mkw 0x97a5400010090049 0x24013f09ec002022 0x03ffc00000388000 0x2c103f03fc013003

def z1251 : W := mkw 0x93a4184a4d240000 0x74033ffdec475000 0xffffc0000fff8000 0x3c803ffffc0ff000

def z1252 : W := mkw 0x480036f528006920 0xd20ed8f403b30750 0xffc73ffffff87fff 0xfbfff8fc63ff0fff

def z1253 : W := mkw 0x61488b0c86423210 0x79e3249314cccccc 0xfff8ff1fffc77e3f 0xffebf4df9efecefc

def z1254 : W := mkw 0x8280000000000000 0x00001a08e8000000 0xffffc00000000000 0xfc047f3ffc000000

def z1255 : W := mkw 0x245351401a9914cb 0x09c00002100ba8af 0x000000000fff8003 0x00b00000000ff00f

def z1256 : W := mkw 0xd3a4020400002000 0xf40ffffdec800440 0xffffff0380000e00 0xfc0ffffffee00e00

def z1257 : W := mkw 0x93a4289a45240000 0x7403e7fdec745000 0xffffc01ff0078000 0x5d03c7fffcf0f000

def z1258 : W := mkw 0x93a4000000000000 0x04001a09ec000000 0x03ffc00000000000 0x2c003803fc000000

def z1259 : W := mkw 0x93a4042000004000 0xf60ffffdef000300 0xffffc0e0000001c0 0xfc0ffffffd000100

def z1260 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0xfc38c00000000000 0xd40ff7ff9c000000

def z1261 : W := mkw 0x93b634f249b44482 0xf60ffffdef331301 0xffffc0e0703881c0 0xfc1ffffffd113103

def z1262 : W := mkw 0xc180020400002000 0x700326994c800440 0xfffffffff0007ffc 0xff4ffffffff00ff0

def z1263 : W := mkw 0x93a4000000000000 0x540202fdec000000 0xffffc0e00e3871c3 0xbef408fffd01010f

def z1264 : W := mkw 0x93a4000000000000 0x540202fdec000000 0xffffc00000000000 0xfc0004fffc000000

def z1265 : W := mkw 0x93a438da4d240000 0x26013f09ef775000 0x03ffffffffff8000 0x2f803f03fffff000

def z1266 : W := mkw 0x000038da4d240000 0xa20dfd0003775000 0xfc003fffffff803c 0xe38fff1c03fff0f0

def z1267 : W := mkw 0x08003cfb6d244920 0xa20dfd6403775310 0x1c003fffffffffc4 0xf3cfffec03ffff30

def z1268 : W := mkw 0xd3a4062400006000 0xf60ffffdef800740 0xffffffff80007ff8 0xff4fffffffe00fc0

def z1269 : W := mkw 0x93a4000000000000 0x7403e79dec000000 0xffffc00000000000 0x4c03c71ffc000000

def z1270 : W := mkw 0x000038da4d240000 0xa20dfd0003775000 0x03c73fffffff8000 0xfb8fff2063fff000

def z1271 : W := mkw 0x4a0026b520006920 0xd20ed8f4a3b00750 0xfc073ffff0007ffc 0xd34fc8fc63f00ff0

def z1272 : W := mkw 0x93a4000000000000 0xd40edbfdec000000 0xffffc00000000000 0xfc044ffffc000000

def z1273 : W := mkw 0x6848ab9da6423b30 0x59e2c09610fcccdc 0xfc003f1fffc77e3f 0x43e3c01c02fecefc

def z1274 : W := mkw 0x025215600a905482 0x820c1862a30b0b05 0x03ff3f0001c07fc3 0xb87c38e3e20e0f0f

def z1275 : W := mkw 0x6848afbda6427b30 0xabede40213fccfdc 0x00003fffffc77fff 0xe3eff40003fecffc

def z1276 : W := mkw 0x80d215600a905482 0x0200020a4b0b0b05 0xffc7ffe00ff87fc3 0xfef44f3c7f0f0f0f

def z1277 : W := mkw 0x605a9b4c8ed23692 0x09e0000210cfcccd 0x00003f1f8fff7e3b 0x03f0000002efcecf

def z1278 : W := mkw 0x0100000000000000 0x2001240104000000 0x03f8c00000000000 0xbc0834c39c000000

def z1279 : W := mkw 0x60488b0c86423210 0x59e2009210cccccc 0xe0003f1f8fc77e3b 0x43e3801002eececc

def z1280 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0xffffc00000000000 0xfc0bb4fffc000000

def z1281 : W := mkw 0x025215600a905482 0x02001802a30b0b05 0x03ff3fe00ff87fc3 0xbaf838c3e30f0f0f

def z1282 : W := mkw 0x025215600a905482 0x820c1862a30b0b05 0x03ff3fe00ff87fc3 0x1af830e3e30f0f0f

def z1283 : W := mkw 0x4300062400006000 0xf20f3cf1a7800740 0xe3ffffff80007ff8 0xff4fbcf3ffe00fc0

def z1284 : W := mkw 0x24537dfa5fbd54cb 0xabcdfd02137ffbaf 0x00003fffffffffff 0xe3ffff0003ffffff

def z1285 : W := mkw 0x41488b0c86423210 0x7023249304cc4c44 0x03f8ff0381c00e00 0x2c0bb4c39eee0e00

def z1286 : W := mkw 0x025215600a905482 0x820cd862a30b0b05 0x03ff3fe00ff87fc3 0xfafff8e3e30f0f0f

def z1287 : W := mkw 0x030018480c000000 0xf20f3cf1a7474000 0xe3ffffff8fff0000 0xff8fbcf3ffefc000

def z1288 : W := mkw 0x000038da4d240000 0xa20dfd0003775000 0x00003f1fffc78000 0xe38bf70002fef000

def z1289 : W := mkw 0x93a4000000000000 0xd40edbfdec000000 0xffffc00000000000 0x1c0000fffc000000

def z1290 : W := mkw 0x93a4000000000000 0x74033ffdec000000 0xffffc00000000000 0xfc0bbffffc000000

def z1291 : W := mkw 0x61488b0c86423210 0x79e3249314cccccc 0xe3f8ff1f8fc77e3b 0xffefffd39eeececc

def z1292 : W := mkw 0x6549cb0c964b3259 0x79e3249314ccecee 0xe3f8ff1fffc7fe3f 0xffebb4d39efefefc

def z1293 : W := mkw 0x000038da4d240000 0xa20dfd0003775000 0x00003fffffff8000 0x238bbf0003fff000

def z1294 : W := mkw 0x93a4000000000000 0x7403ff9dec000000 0x03ffc00000000000 0x2c03bf03fc000000

def z1295 : W := mkw 0x6c5377f53a997deb 0xdbcec0f613bbafff 0xfc003fffffffffff 0xd3ffc0fc03ffffff

def z1296 : W := mkw 0x93b6146008904482 0xf60ffffdef030301 0xffffffe00ff801c0 0xfe9fffffff0f0103

def z1297 : W := mkw 0x0300000000000000 0x500200f1a4000000 0xe3ffc00000000000 0x1c0000f3fc000000

def z1298 : W := mkw 0x480036f528006920 0xd20ed8f403b30750 0xfc003ffff0387ffc 0xd34fc8fc03f10ff0

def z1299 : W := mkw 0x93a4000000000000 0x54021bfdec000000 0xffffc00000000000 0x1c000bfffc000000

def z1300 : W := mkw 0xb7edc908964b1259 0x2de13f0bfc4ce8ae 0x03ffc0000fff8003 0x2cb03f03fc0ff00f

def z1301 : W := mkw 0x2048890886421210 0x09e00002104cc88c 0x00003f1f8fc70003 0x03a0000002eec00c

def z1302 : W := mkw 0x61488b0c86423210 0x79e3249314cccccc 0xe3f8ff1f81c70e38 0xfd0bb4d39eeecec0

def z1303 : W := mkw 0x0000184a4d240000 0x20013d0000475000 0x00003f038fff8000 0x208bbf0002eff000

def z1304 : W := mkw 0xe589ea9ed56f2259 0x79e3e7995cf4f4ea 0xfc00c01ff007803c 0x4503c71c1cf0f0f0

def z1305 : W := mkw 0x1324000000000000 0x540200f5a4000000 0xe3f8c00000000000 0x1c0000d39c000000

def z1306 : W := mkw 0x625a9f6c8ed27692 0x8bec1862b3cfcfcd 0x00073fff8fff7ffb 0x03f4082063efcfcf

def z1307 : W := mkw 0x480036f528006920 0xd20ed8f403b30750 0xfc003ffff1c07ffc 0xd34ff0fc03fe0ff0

def z1308 : W := mkw 0x97a5400010090049 0xf40ffffdec002022 0xffffc0fc7e3f81c4 0xff9ffffffd11f133

def z1309 : W := mkw 0x93a4184a4d240000 0x74033f99ec475000 0xe3ffff1f8fff8000 0xff8bbfd3feeff000

def z1310 : W := mkw 0x4800229520002920 0xd20ec09403b00450 0xfc003ffff0007e3c 0xd34fc0dc03f00ef0

def z1311 : W := mkw 0x025215600a905482 0x820c1862a30b0b05 0xffff3ffc7fffffff 0xfbfc7fffe31fffff

def z1312 : W := mkw 0x9ba424b120004920 0xd60ec2fdef300310 0xffffc0e0700001c4 0x1c0440fffd100130

def z1313 : W := mkw 0x0100000000000000 0x7003249104000000 0xe3f8c01c00007038 0xff4bb4d39c0000c0

def z1314 : W := mkw 0x60488b0c86423210 0x09e0000210cccccc 0x00003f038fc70e03 0x00a0000002eece0c

def z1315 : W := mkw 0x93a438da4d240000 0xa60dff09ef775000 0xffffffffffff8000 0xff8fff3ffffff000

def z1316 : W := mkw 0x480026b520006920 0xd20ec0f403b00750 0xfc003ffffe387fff 0xd3ffc0fc03f10fff

def z1317 : W := mkw 0x93a4184a4d240000 0x24013f09ec475000 0x03ffc00001c00000 0x2c003f03fc0e0000

def z1318 : W := mkw 0x93a4080804000000 0x24013f09ec444000 0x03ffff1f8fc70000 0xef8bbf03feeec000

def z1319 : W := mkw 0x93a4080804000000 0x24013f09ec444000 0x03ffc0000fc70000 0x2c803f03fc0ec000

def z1320 : W := mkw 0x025235f00a905482 0x820cd862a33b0b05 0x03ff3fffffffffc3 0xfbffffe3e3ffff0f

def z1321 : W := mkw 0x6048ab9c86423210 0x0be0000213fccccc 0x00003fffffc77e3b 0x03e0000003fececc

def z1322 : W := mkw 0x91a4000000000000 0x740327994c000000 0xe3f8c00000000000 0xfc0bb7d39c000000

def z1323 : W := mkw 0x6549cb0c964b3259 0x79e3249314ccecee 0xfff8ffffffffffff 0xfffff4ff9fffffff

def z1324 : W := mkw 0x480026b520006920 0x5002c0f400b00750 0xfc003f1ff0007ffc 0xd34bc0fc02f00ff0

def z1325 : W := mkw 0x9aa434f369244920 0x860cdb6ceb331310 0x1c0700e0703881c4 0x00044b2c61113130

def z1326 : W := mkw 0x025215600a905482 0x820c1862a30b0b05 0x03ff3f000ff80e03 0xb8bc38e3e20f0e0f

def z1327 : W := mkw 0x0100184a4d240000 0x20013d0104475000 0x03f8c0000fff8000 0x2c803f039c0ff000

def z1328 : W := mkw 0x025215600a905482 0x820cd866a30b0b05 0x1fff3fe00ff87fc3 0xbafc78efe30f0f0f

def z1329 : W := mkw 0x93a4000000000000 0x24013f6dec000000 0x1fffc00000000000 0x2c003f2ffc000000

def z1330 : W := mkw 0x6449c304924b3259 0x09e000021088acee 0x0000000000007fff 0x0070000000000fff

def z1331 : W := mkw 0x00003cfa4d244000 0xa20dfd6003775300 0x00003fffffff8e00 0xe38fffc003fffe00

def z1332 : W := mkw 0x93a4000000000000 0x540202fdec000000 0xffffc00000000000 0xdc0440fffc000000

def z1333 : W := mkw 0x91a4289a45240000 0x7403e79d4c745000 0xfff8ff1fffc78000 0xff8bf7df9efef000

def z1334 : W := mkw 0x605a9f6c8ed27692 0xabed3c0213cfcfcd 0x00003fff8fff7ffb 0xe3ffbc0003efcfcf

def z1335 : W := mkw 0x0300000000000000 0x70033c91a4000000 0xe3ffc00000000000 0xfc0bbcd3fc000000

def z1336 : W := mkw 0xdba43eff6d246920 0xf60ffffdeff75750 0xffffff0381c00e00 0xfc0ffffffeee0e00

def z1337 : W := mkw 0x93a4209000000000 0xf60ffffdef300000 0xfffffffff00071fc 0xff4ffffffff001f0

def z1338 : W := mkw 0x480026b520006920 0x5002c0f400b00750 0xfc0000fff0007ffc 0xd347c0fc01f00ff0

def z1339 : W := mkw 0x8280000000000000 0xd00edafce8000000 0xffffc00000000000 0xfc0ffffffc000000

def z1340 : W := mkw 0x0100184a4d240000 0x70033d9104475000 0xe3f8c0000fff8000 0xfc8bbfd39c0ff000

def z1341 : W := mkw 0x60488b0c86423210 0x09e0000210cccccc 0x00003ffffffffe3b 0xe3e44f0003fffecc

def z1342 : W := mkw 0xd3ac8a0c84422210 0xf42ffffdecc44440 0xffffc00380000000 0xfc0ffffffce00000

def z1343 : W := mkw 0x025215600a905482 0x820c1862a30b0b05 0x03ff3f000fc07fc3 0xbaf830e3e20e0f0f

def z1344 : W := mkw 0x0100000000000000 0x7003249104000000 0xe3f8c0fc7e3f8000 0xff8fffd39d11f000

def z1345 : W := mkw 0x93a438da4d240000 0xf60ffffdef775000 0xffffc0fff03f8000 0xfd0ffffffdf1f000

def z1346 : W := mkw 0xd9a4229520002920 0x7403e79d4cb00450 0xfff8ff1ff0007e3c 0xff4bf7df9ef00ef0

def z1347 : W := mkw 0x93a4000000000000 0xf40fe6fdec000000 0xffffc00000000000 0xfc0ff4fffc000000

def z1348 : W := mkw 0x93a4000000000000 0xa40dff6dec000000 0x1fffc00000000000 0xbc0c7feffc000000

def z1349 : W := mkw 0x93b6104008900482 0x24013f09ec030001 0x03ffc00000380000 0x2c103f03fc010003

def z1350 : W := mkw 0xf7edc304924b3259 0x5de202fffc88acee 0xffffc00000007fff 0x1c7000fffc000fff

def z1351 : W := mkw 0x8280104008000000 0x820c1a68eb030000 0xfffffffc7fff8000 0xff8c7fffff1ff000

def z1352 : W := mkw 0x6449cb0c964b3259 0x09e0000210ccecee 0x00003f1fffc7fe3f 0x03e0000002fefefc

def z1353 : W := mkw 0x93a4000000000000 0xd40ec2fdec000000 0xffffc00000000000 0x1c0440fffc000000

def z1354 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0xffffc0e070388000 0xfc0ffffffd113000

def z1355 : W := mkw 0x93a4000000000000 0x740326fdec000000 0xffffc00000000000 0xfc0ffffffc000000

def z1356 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0xffffc0000e380003 0xfcbffffffc01000f

def z1357 : W := mkw 0x0100000000000000 0xf00fe49104000000 0xe3f8c00000000000 0xfc0ff4d39c000000

def z1358 : W := mkw 0xdba42ebd24006920 0xf60ffffdeff44750 0xffffffffffc77ffc 0xffcffffffffecff0

def z1359 : W := mkw 0x93a4000000000000 0x7403ff9dec000000 0xffffc00000000000 0xfc07ff3ffc000000

def z1360 : W := mkw 0x000038da4d240000 0xa20dfd0003775000 0x00003f1f8fff8000 0xe38bbf0002eff000

def z1361 : W := mkw 0x205215600a905482 0x0bc00002130b8b8d 0x00003ffc0fff7ffb 0x03f00000030fcfcf

def z1362 : W := mkw 0x93a4104008000000 0xf60ffffdef030000 0xffffff0001c00000 0xfc0ffffffe0e0000

def z1363 : W := mkw 0x0100000000000000 0x7003249104000000 0xe3ffc00000000000 0xfc0fbcf3fc000000

def z1364 : W := mkw 0x000038da4d240000 0xa20dfd0003775000 0xe0003ffffffff038 0xf3cfff1003fff0c0

def z1365 : W := mkw 0x97a5400010090049 0xf40ffffdec002022 0xffffc0fc7038f1fc 0xff5ffffffd1131f3

def z1366 : W := mkw 0x93a4000000000000 0x24013f09ec000000 0xe3ffc00000000000 0xfc003f13fc000000

def z1367 : W := mkw 0x480026b520006920 0xd20ec0f403b00750 0xffc73ffff0007ffc 0xfb4fc8fc63f00ff0

def z1368 : W := mkw 0x61488b0c86423210 0x79e3249314cccccc 0xe038ff1f8fc77e3b 0x47ebb4d39eeececc

def z1369 : W := mkw 0x132438da4d240000 0xf60ffdf5a7775000 0xe3f8ffffffff8000 0xff8fffd39ffff000

def z1370 : W := mkw 0x025215624bb45482 0x820c1962a30b1b05 0x03ff3fe00ff8ffc3 0xbafc3be3e30f3f0f

def z1371 : W := mkw 0x025211400a901482 0x00001802a00b0805 0x03ff00000ff87e03 0x38f038c3e00f0e0f

def z1372 : W := mkw 0x025215600a905482 0x820c1862a30b0b05 0x03ff3fe00ff87fc3 0xfafc7fe3e30f0f0f

def z1373 : W := mkw 0x93a4000000000000 0x540202fdec000000 0xffffc00000000000 0x1c044bfffc000000

def z1374 : W := mkw 0x93a4080a45240000 0xf40ffffdec445000 0xffffc00000078000 0xfc0ffffffc00f000

def z1375 : W := mkw 0x61488b0c86423210 0x79e3249314cccccc 0xffffffffffff7fff 0xfffffcffffffcfff

def z1376 : W := mkw 0x0a5235f36bb45da2 0x820cd966a33b1b15 0x1fff3fe07ff8ffc7 0xbafc7befe31f3f3f

def z1377 : W := mkw 0x93a438da4d240000 0x7403ff9dec775000 0xffffc01fffff8000 0x6d83ff1ffcfff000

def z1378 : W := mkw 0x480026b520006920 0xd20ec0f403b00750 0xfc003f0380007ffc 0xd04fc0fc02e00ff0

def z1379 : W := mkw 0x93a4000000000000 0xf40fff9dec000000 0xffffc00000000000 0xec0fff1ffc000000

def z1380 : W := mkw 0x6848bfffef667b30 0xdbeec0f613ffdfdc 0xfc003fffffffffff 0xd3efc0fc03fffffc

def z1381 : W := mkw 0x93a4000000000000 0xa40d3f69ec000000 0x03ffc00000000000 0x2c043f23fc000000

def z1382 : W := mkw 0x0100000000000000 0x7003249104000000 0xe038c00000000000 0x440bb4d39c000000

def z1383 : W := mkw 0x000038da4d240000 0xa20dfd0003775000 0xe3c0ffffffff8000 0xff8fff101ffff000

def z1384 : W := mkw 0x08003cfb6d244920 0xa20dfd6403775310 0x00003fffffff8000 0xe38fff0003fff000

def z1385 : W := mkw 0xa6d3594a5fbd14cb 0x29c13f0af84ff8af 0x03ffc0000fff8003 0x2cb03f03fc0ff00f

def z1386 : W := mkw 0x004011400a001000 0x820c1802030b0804 0x03ff3fe00ff87fc3 0xbafc38e3e30f0f0f

def z1387 : W := mkw 0xdba426b520006920 0xf60fe7fdefb00750 0xfffffffff0007ffc 0xdf4fc7fffff00ff0

def z1388 : W := mkw 0x8280000000000000 0x00000268e8000000 0xffffc00000000000 0xfc044ffffc000000

def z1389 : W := mkw 0x0100000000000000 0x500200f504000000 0xfff8c00000000000 0x1c0000ff9c000000

def z1390 : W := mkw 0x93a4000000000000 0x740326fdec000000 0xffffc00000000000 0x1c0bb0fffc000000

def z1391 : W := mkw 0x93a4209000000000 0xf60ffffdef300000 0xffffff0380000000 0xfc0ffffffee00000

def z1392 : W := mkw 0x4100020400002000 0x7003249104800440 0xe3f8c00000007e38 0xfc4bb4d39c000ec0

def z1393 : W := mkw 0x6048830482423210 0x09e0000210888ccc 0x00003f1f80007e3b 0x0360000002e00ecc

def z1394 : W := mkw 0x0100000000000000 0xa00dfd0104000000 0x03f8c00000000000 0xec0fff039c000000

def z1395 : W := mkw 0x0252052002905482 0x00000062a0080b05 0x03ff3f0001c07fc3 0x187830e3e20e0f0f

def z1396 : W := mkw 0x93a418480c000000 0xf60ffffdef474000 0xffffffff8fff0000 0xff8fffffffefc000

def z1397 : W := mkw 0x97a5400010090049 0xf40ffffdec002022 0xffffc00070008004 0xfc0ffffffc103030

def z1398 : W := mkw 0x8180000000000000 0x700326994c000000 0xe3ffc00000000000 0xfc0bbfd3fc000000

def z1399 : W := mkw 0x127615600a905482 0x860cd966a30b0b05 0x03ff3fe00ff87fc3 0xbafc38e3e30f0f0f

def z1400 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0xffffc00000000000 0x1c0ffbfffc000000

def z1401 : W := mkw 0x0100042000004000 0xf20f24f107000300 0xe3f8ffe000007fc0 0xfe4fb4f39f000f00

def z1402 : W := mkw 0x93a4000000000000 0xf60ffffdef000000 0xffffffe000000000 0xfe0fffffff000000

def z1403 : W := mkw 0xa481400010090049 0x09c002085800a0aa 0xffc7c0fc7e3f81ff 0x6db44f3c7d11f1ff

def z1404 : W := mkw 0x025211400a901482 0x820c1802a30b0805 0x03ff3fe00ff87e03 0xbafc38c3e30f0e0f

def z1405 : W := mkw 0x025215600a905482 0x820c1862a30b0b05 0x03ff3f0001c00e03 0x083830c3e20e0e0f

def z1406 : W := mkw 0x93a430d249240000 0xf60ffffdef331000 0xffffc00000000000 0xfc0ffffffc000000

def z1407 : W := mkw 0x025211400a901482 0x00001802a00b0805 0x03ff3fe00ff87fc3 0xbafc38e3e30f0f0f

def z1408 : W := mkw 0x0100000000000000 0x7003249104000000 0xfff8c0fc700071fc 0xff4ff4ff9d1001f0

def z1409 : W := mkw 0x8280000000000000 0xa00dff68e8000000 0xffffc00000000000 0xfc0ffffffc000000

def z1410 : W := mkw 0x090024b120004920 0xf20fe4f507300310 0xfff8c0e0700001c4 0xfc0ff4ff9d100130

def z1411 : W := mkw 0x93a438da4d240000 0xf60ffffdef775000 0xffffff038fff8000 0xfc8ffffffeeff000

def z1412 : W := mkw 0x8581400010090049 0x700326994c002022 0xffffc0e0703881c4 0xfc1ffffffd113133

def z1413 : W := mkw 0x97a5400010090049 0x24013f09ec002022 0x1fffc0e0703881c4 0x2c147f2ffd113133

def z1414 : W := mkw 0x0100000000000000 0x2001240104000000 0xe3f8c00000000000 0xfc0034139c000000

def z1415 : W := mkw 0x93a4080804000000 0x740326fdec444000 0xffffff1f8fc70000 0xff8bb4fffeeec000

def z1416 : W := mkw 0x8280000000000000 0x00000268e8000000 0xffffc00000000000 0x1c0000fffc000000

def z1417 : W := mkw 0x020038da4d240000 0xa20dfd60a3775000 0x03ff3ffffffff1c3 0xfbffffe3e3fff10f

def z1418 : W := mkw 0x93a4104008000000 0xf40ffffdec030000 0xffffc0000ff80000 0xfc8ffffffc0f0000

def z1419 : W := mkw 0x480026b520006920 0xd20ed8f403b00750 0xfc003ffff0007ffc 0xf34ff8fc03f00ff0

def z1420 : W := mkw 0x93a4000000000000 0x540202fdec000000 0xffffc0fc700071fc 0xdf4440fffd1001f0

def z1421 : W := mkw 0x480026b520006920 0xd20ec0f403b00750 0xfc003f1ff0007ffc 0x514bc0fc02f00ff0

def z1422 : W := mkw 0xdba4229520002920 0xf40ffffdecb00450 0xffffff1ff0007e3c 0xff4ffffffef00ef0

def z1423 : W := mkw 0x0000289804000000 0xa20de40003744000 0x00003fffffff8000 0xe38fff0003fff000

def z1424 : W := mkw 0xdba4229520002920 0xf60ffffdefb00450 0xfffffffff000003c 0xff0ffffffff000f0

def z1425 : W := mkw 0xdba426b520006920 0xd60ec2fdefb00750 0xfffffffff0007ffc 0xff4fcffffff00ff0

def z1426 : W := mkw 0x6848ab9da6423b30 0x09e0000210fcccdc 0x00003f1fffc77e3f 0x03e0000002fecefc

def z1427 : W := mkw 0x97a5400010090049 0xf40ffffdec002022 0xffffc00000388000 0xfc1ffffffc013003

def z1428 : W := mkw 0x60489b4ecf663210 0x09e0000210cfdccc 0x00003f1f8ffffe3b 0x03e0000002effecc

def z1429 : W := mkw 0x93a438da4d240000 0xa60dff69ef775000 0x03ffffffffff8000 0xff8fffe3fffff000

def z1430 : W := mkw 0xe4c9cb0c964b3259 0x09e0020a58ccecee 0x1c073fffffffffff 0x03f44b2c63ffffff

def z1431 : W := mkw 0x0000289a45240000 0xa00dfd0000745000 0x00003f1fffc78000 0xe38fff0002fef000

def z1432 : W := mkw 0x0000289a45240000 0x2001e50000745000 0x00003f1ff1c78000 0x410bf70002fef000

def z1433 : W := mkw 0x6549cb0c964b3259 0x79e3249314ccecee 0xe3ffffffffffffff 0xffffbcf3ffffffff

def z1434 : W := mkw 0x000038da4d240000 0x22013d0003775000 0x00003fffffff8000 0xe38bbf0003fff000

def z1435 : W := mkw 0x93a4000000000000 0x24013f09ec000000 0xffffc0fc700071fc 0xff447f3ffd1001f0

def z1436 : W := mkw 0x025215600a905482 0x820c1862a30b0b05 0x003f3fe00ff87fc3 0x02fc38e3e30f0f0f

def z1437 : W := mkw 0xdba436f769246920 0xf60ffffdefb31750 0xfffffffff038fffc 0xff4ffffffff13ff0

def z1438 : W := mkw 0x8280000000000000 0x800c1a68e8000000 0xffffc00000000000 0xbc0c38fffc000000

def z1439 : W := mkw 0x4800229520002920 0x5002c09400b00450 0xfc003f1ff0000e3c 0x410bc0dc02f00ef0

def z1440 : W := mkw 0x480026b520006920 0xd20ec0f403b00750 0xfc0000fff0007ffc 0x5147c0fc01f00ff0

def z1441 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0xffffc01c70078000 0xfd0ffffffc10f000

def z1442 : W := mkw 0x91a438da4d240000 0xf60fff9d4f775000 0xfff8ffffffff8000 0xff8fffdf9ffff000

def z1443 : W := mkw 0x9ba424b120004920 0xf60ffffdef300310 0xfffffffff00001c4 0xff0ffffffff00130

def z1444 : W := mkw 0x480026b520006920 0xd20ec0f403b00750 0xfc003ffff0000ffc 0x410fc0fc03f00ff0

def z1445 : W := mkw 0x08003cfb6d244920 0xa20dfd6403775310 0xfc003ffffffff1fc 0xf3cfff3c03fff1f0

def z1446 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0xffffc0e00e380000 0xfe8ffffffd010000

def z1447 : W := mkw 0x480026b520006920 0xd20ec0f403b00750 0xffc73ffff0007fff 0xdb7fc0fc63f00fff

def z1448 : W := mkw 0x5b2426b520006920 0xf60ffdf5a7b00750 0xfff8fffff0007ffc 0xff4ff4ff9ff00ff0

def z1449 : W := mkw 0x6c49efbdb64b7b79 0x0be0000213fceffe 0x00003fffffffffff 0x03f0000003ffffff

def z1450 : W := mkw 0x93a4042000004000 0xf40ffffdec000300 0xffffc00000007fc0 0xfc4ffffffc000f00

def z1451 : W := mkw 0x8e9374f138994deb 0x820cda6ceb332333 0x1c0700e0703881c4 0x00144b2c61113133

def z1452 : W := mkw 0x41088a0c84422210 0x7023249104c44440 0xe3f8c00380000000 0xfc0bb4d39ce00000

def z1453 : W := mkw 0x93a4042000004000 0x540202fdec000300 0xffffc00000007fc0 0x1c4000fffc000f00

def z1454 : W := mkw 0x93a4000000000000 0xf40f3ff9ec000000 0xe3ffc00000000000 0xfc0fbff3fc000000

def z1455 : W := mkw 0x025235f24bb45482 0x820cd962a33b1b05 0x03ff3ffc7fffffc3 0xfbfc7fe3e31fff0f

def z1456 : W := mkw 0x9ba4209120000920 0xf40ffffdec300010 0xffffc00070000004 0xfc0ffffffc100030

def z1457 : W := mkw 0x61488b0c86423210 0x79e3249314cccccc 0xe3ffff1f8fff7e3b 0xfffbbcd3feefcecf

def z1458 : W := mkw 0x93a4000000000000 0x24013f09ec000000 0xffffc00000000000 0x6c007f1ffc000000

def z1459 : W := mkw 0x8180000000000000 0x700326994c000000 0xfff8c00000000000 0xfc0bf7df9c000000

def z1460 : W := mkw 0x60488b0c86423210 0x09e0000210cccccc 0x000000000fc77e3b 0x00e00000000ececc

def z1461 : W := mkw 0x93b6146008904482 0xf60ffffdef030301 0xffffc0e00e3871c3 0xfefffffffd01010f

def z1462 : W := mkw 0x025235f24bb45482 0x820c1862a33b1b05 0x03ff3fe07ff8ffc3 0xbafc38e3e31f3f0f

def z1463 : W := mkw 0x68488725a2427b30 0x09e0000210888fdc 0x0000000000007fff 0x0060000000000ffc

def z1464 : W := mkw 0x93a438da4d240000 0xf60ffffdef775000 0x03ffff038fff8000 0x2c8bbfc3feeff000

def z1465 : W := mkw 0x2048890886421210 0x09e00002104cc88c 0x00003f000fc77e03 0x02e00000020ece0c

def z1466 : W := mkw 0x000038da4d240000 0x2201e50003775000 0x00003fffffff8000 0xe387cf0003fff000

def z1467 : W := mkw 0x2040090806001000 0x29c12402104cc88c 0xe3f8ff1f8fc77e3b 0xffebb4d39eeececc

def z1468 : W := mkw 0x61488b0c86423210 0x79e3249314cccccc 0xe3f8ff038fc77e3b 0x3cebb4d39eeececc

def z1469 : W := mkw 0x480026b520006920 0xd20ec0f403b00750 0xfc073ffff0387ffc 0xd35fc8fc63f10ff3

def z1470 : W := mkw 0x6048ab9ec7663210 0x29e1e50210fcdccc 0x00003f1fffc7fe3b 0x43e3c70002fefecc

def z1471 : W := mkw 0xd3a4020400002000 0xf40ffffdec800440 0xffffc01f80000038 0xfd0ffffffce000c0

def z1472 : W := mkw 0x61488b0c86423210 0x79e3249314cccccc 0xe3ffff1f8fc77ffb 0xfffbb4f3feeecfcf

def z1473 : W := mkw 0xd3a4020400002000 0xf40ffffdec800440 0xffffc00000007e38 0xfc4ffffffc000ec0

def z1474 : W := mkw 0x93a4000000000000 0x04000209ec000000 0x03ffc00000000000 0x2c000f03fc000000

def z1475 : W := mkw 0x080038db6d240920 0xa20dfd0403775010 0x1c003fffffff8004 0xe38fff0c03fff030

def z1476 : W := mkw 0x030038da4d240000 0xf20ffdf1a7775000 0xe3ffffffffff8000 0xff8ffff3fffff000

def z1477 : W := mkw 0x9fa564b130094969 0xf60ffffdef302332 0xffffc0e0703881c4 0xfc1ffffffd113133

def z1478 : W := mkw 0xdba426b520006920 0xf60ffffdefb00750 0xfc38ff1ff0000e3c 0x450bf7df9ef00ef0

def z1479 : W := mkw 0x61488b0c86423210 0x79e3249314cccccc 0xe038ff1f8fc70e38 0xe78bb4d39eeecec0

def z1480 : W := mkw 0x000038da4d240000 0xa20dfd0003775000 0x00003f1fffff8000 0x618bff0002fff000

def z1481 : W := mkw 0x000038da4d240000 0xa20dfd0003775000 0x00003ffff1c78000 0xc30ff70003fef000

def z1482 : W := mkw 0x4900229520002920 0x7003e49504b00450 0xfff8c01ff000003c 0xfd0bf4df9cf000f0

def z1483 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0xffffc00000000000 0xdc0ff0fffc000000

def z1484 : W := mkw 0x0040052002005000 0x820c006203080b04 0x03ff3fe00ff87fc3 0xbafc38e3e30f0f0f

def z1485 : W := mkw 0x000030d008000000 0x820cd80003330000 0x00003fffffff8000 0xe38fff0003fff000

def z1486 : W := mkw 0x8080000000000000 0x0000020848000000 0xffffc00000000000 0xfc0c7ffffc000000

def z1487 : W := mkw 0x2048b9dacf661210 0x0be00002137fd88c 0x00003fffffff8003 0x03a0000003fff00c

def z1488 : W := mkw 0x025215600a905482 0x00001862a00b0b05 0x03ff00000ff80e03 0x28b038c3e00f0e0f

def z1489 : W := mkw 0x0000184a4d240000 0xa00dfd0000475000 0x00003f1f8fff8000 0xe38fff0002eff000

def z1490 : W := mkw 0x93a4000000000000 0x740326fdec000000 0xffffc00000000000 0x3c0034fffc000000

def z1491 : W := mkw 0x93a4000000000000 0x74033f99ec000000 0x03ffc00000000000 0x2c0bbfc3fc000000

def z1492 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0x03ffc00000000000 0xec0fffc3fc000000

def z1493 : W := mkw 0x93a4000000000000 0xa40dff09ec000000 0x03ffc00000000000 0x2c0bbf03fc000000

def z1494 : W := mkw 0x605a8f2c86d27692 0x09e0000210cccfcd 0x00003f1f8fc77ffb 0x03f0000002eecfcf

def z1495 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0xffffff1f80000000 0xff0ffffffee00000

def z1496 : W := mkw 0x60488b0c86423210 0x59e2009210cccccc 0x00003f1f8fc77e3b 0x03eb80c002eececc

def z1497 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0xffffc00000000000 0x3c047ffffc000000

def z1498 : W := mkw 0x0100000000000000 0x7003249104000000 0xe3f8c00000000000 0x1c0bb0d39c000000

def z1499 : W := mkw 0x0000184a4d240000 0x20013d0000475000 0x0000001f8fff8000 0x6183bf0000eff000

def z1500 : W := mkw 0x6449cb0c964b3259 0x09e0000210ccecee 0x00003f1f8ffffe3b 0x03f0000002effecf

def z1501 : W := mkw 0x1324000000000000 0xf40ffdf5a4000000 0xe3f8c00000000000 0xfc0fffd39c000000

def z1502 : W := mkw 0x0252052002905482 0x00000062a0080b05 0x03ff3fe00ff87fc3 0xbafc38e3e30f0f0f

def z1503 : W := mkw 0x4800062520006920 0x500200f400800750 0xfc003ffff0007ffc 0xd34fc0fc03f00ff0

def z1504 : W := mkw 0x8280000000000000 0x800c1a68e8000000 0x03ffc00000000000 0xbc0c3fe3fc000000

def z1505 : W := mkw 0x68488f2da6427b30 0x59e200f610cccfdc 0xfc003f1f8fc77fff 0x13e000fc02eecffc

def z1506 : W := mkw 0x61488b0c86423210 0x79e3249314cccccc 0xe3f8ff1fffc7fe3b 0xffebf7d39efefecc

def z1507 : W := mkw 0x025215600a905482 0x820c1862a30b0b05 0x03ff3fe00ff80e03 0xaabc38c3e30f0e0f

def z1508 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0xffffc01c0e070000 0xff8ffffffc00c000

def z1509 : W := mkw 0x93a4000000000000 0x24013f09ec000000 0x03ffc0fc7e3f8000 0xef847f03fd11f000

def z1510 : W := mkw 0xdba4020520002920 0x540202fdec800450 0xffffc0000000003c 0x1c0000fffc0000f0

def z1511 : W := mkw 0x60488b0c86423210 0x59e2009210cccccc 0xe0003f1f8fc77e3b 0x13e000d002eececc

def z1512 : W := mkw 0x0100000000000000 0xf00ffd9104000000 0xe3f8c00000000000 0xfc0bb4d39c000000

def z1513 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0x03ffc00000000000 0x0c0bb0c3fc000000

def z1514 : W := mkw 0x480026b520006920 0xd20ec0f403b00750 0xfc003ffffe3ffffc 0xd3cfc0fc03f1fff0

def z1515 : W := mkw 0x9ba424b120004920 0xf60ffffdef300310 0xffffc0fc700071fc 0xff4ffffffd1001f0

def z1516 : W := mkw 0x93a4000000000000 0x74033f9dec000000 0xffffc00000000000 0x2c003f1ffc000000

def z1517 : W := mkw 0x480026b520006920 0xd20ed9f403b00750 0xfc003ffff0007ffc 0xd34fcbfc03f00ff0

def z1518 : W := mkw 0x1124000000000000 0x7403e59504000000 0xe3f8c00000000000 0xfc0bb4d39c000000

def z1519 : W := mkw 0x93a4000000000000 0x5402c2fdec000000 0xffffc00000000000 0x5c03c0fffc000000

def z1520 : W := mkw 0x8180000000000000 0x200126094c000000 0xffffc00000000000 0xfc047f3ffc000000

def z1521 : W := mkw 0x480026b520006920 0xd20ec0f403b00750 0xfc003fe3f0007ffc 0x104fc0fc03f00ff0

def z1522 : W := mkw 0xdba4062520006920 0x74033ffdec800750 0xffffc00000007ffc 0x3c403ffffc000ff0

def z1523 : W := mkw 0x86935460189944cb 0x820c1a68eb032323 0xffffc0e0703881c4 0xfc1c7ffffd113133

def z1524 : W := mkw 0x6048bbdecf663210 0x8becd90213ffdccc 0x00003ffffffffe3b 0x03e44b0003fffecc

def z1525 : W := mkw 0x2449c908964b1259 0x09e00002104ce8ae 0x000000fc7ffff1ff 0x03f00000011ff1ff

def z1526 : W := mkw 0x0a5215612a905da2 0x820c1866a30b0b15 0x1fff3fe00ff87fc7 0xbafc38efe30f0f3f

def z1527 : W := mkw 0x4800229520002920 0x5002c09400b00450 0xfc00001ff0007e3c 0x5143c0dc00f00ef0

def z1528 : W := mkw 0x000038da4d240000 0x2001fd0000775000 0x000000038fff8000 0x2083bf0000eff000

def z1529 : W := mkw 0x61488b0c86423210 0x79e3249314cccccc 0xe3f8ffffffc77fff 0xffebb4d39ffecffc

def z1530 : W := mkw 0x60488b0c86423210 0x09e0000210cccccc 0xfc003fffffc77fff 0xd3e4403c03fecffc

def z1531 : W := mkw 0x025215600a905482 0x820c1862a30b0b05 0x03ff3f000ff87fc3 0x38f838e3e20f0f0f

def z1532 : W := mkw 0x00003cfa4d244000 0xa20dfd6003775300 0x00003fffffff81c0 0xe38fff2003fff100

def z1533 : W := mkw 0xdba426b520006920 0xf60ffffdefb00750 0xfffffffffe387fff 0xfffffffffff10fff

def z1534 : W := mkw 0x02123cfa4db44482 0xa20dfd60a3775301 0x03c73ffffffff1c3 0xfbffff2063fff10f

def z1535 : W := mkw 0x61488b0c86423210 0x79e3249314cccccc 0xe3fffffffffffffb 0xfffffff3ffffffcf

def z1536 : W := mkw 0x93a4000000000000 0xd40edafdec000000 0xffffc00000000000 0xfc0ff8fffc000000

def z1537 : W := mkw 0x49002ebd24006920 0xf20fe4f507f44750 0xfff8ffffffc77ffc 0xffcff4ff9ffecff0

def z1538 : W := mkw 0x93a4000000000000 0x7403e7fdec000000 0xffffc00000000000 0x1c0380fffc000000

def z1539 : W := mkw 0x0300000000000000 0xa00d3c61a4000000 0x03ffc00000000000 0xbc0c3ce3fc000000

def z1540 : W := mkw 0x61488b0c86423210 0x79e3249314cccccc 0xe3f8fffffffffe3b 0xffebb4d39ffffecc

def z1541 : W := mkw 0x480026b520006920 0x520200f403b00750 0xfc003ffff0007ffc 0xd34b80fc03f00ff0

def z1542 : W := mkw 0x0000184a4d240000 0x20013d0000475000 0x00003fffffff8000 0xe38fff0003fff000

def z1543 : W := mkw 0x869374f259bd44cb 0x820cdb68eb333323 0x1c0700e0703881c4 0x00144b2c61113133

def z1544 : W := mkw 0xdba4062520006920 0x540202fdec800750 0xffffc0fc70007ffc 0xff444ffffd100ff0

def z1545 : W := mkw 0x010038da4d240000 0x7203249107775000 0xe3f8ffffffff8000 0xff8bb4d39ffff000

def z1546 : W := mkw 0x00003cfa4d244000 0xa20dfd0003775300 0x00003fffffffffc0 0xe3cfff0003ffff00

def z1547 : W := mkw 0x60488b0c86423210 0x09e0000210cccccc 0x00003f0381c07e3b 0x0060000002ee0ecc

def z1548 : W := mkw 0x93a4184a4d240000 0xf60ffffdef475000 0xffffffe00fff8000 0xfe8fffffff0ff000

def z1549 : W := mkw 0x93a4000000000000 0x04000209ec000000 0xffffc00000000000 0xfc044f3ffc000000

def z1550 : W := mkw 0x60489b4ecf663210 0x29e13d0210cfdccc 0x00003f1f8ffffe3b 0x23e03f0002effecc

def z1551 : W := mkw 0x91a4000000000000 0xf40fe7fd4c000000 0xfff8c00000000000 0xfc0ff7ff9c000000

def z1552 : W := mkw 0xed89ea9db44b2b79 0x79e3e69d5cf4e4fa 0xfc00c01ff007803c 0x4503c71c1cf0f0f0

def z1553 : W := mkw 0x6040030402003000 0x59c2009210888ccc 0xe3f8ff1f8fc77e3b 0xffebb4d39eeececc

def z1554 : W := mkw 0x480026b520006920 0xd20ec0f403b00750 0xfc003ffff0000e3c 0xc30fc0dc03f00ef0

def z1555 : W := mkw 0x60488b0c86423210 0xa9edfd0210cccccc 0x00003f1f8fc77e3b 0xe3efff0002eececc

def z1556 : W := mkw 0x000038da4d240000 0xa20dfd0003775000 0x00003ffffffffe00 0xf3cfffc003fffe00

def z1557 : W := mkw 0xdba4062520006920 0xf40ffffdec800750 0xffffc00000000e00 0xfc0ffffffc000e00

def z1558 : W := mkw 0x61488b0c86423210 0x79e3249314cccccc 0xe3f8ff1f81c07e3b 0xdf6bb0d39eee0ecc

def z1559 : W := mkw 0x480026b520006920 0x5202c09403b00750 0xfc003ffff0007ffc 0xd34bc0dc03f00ff0

def z1560 : W := mkw 0x025215600a905482 0x820c1862a30b0b05 0xffff3fe00ff87fff 0xbafc38ffe30f0fff

def z1561 : W := mkw 0x480026b520006920 0x5202c09403b00750 0xfc003f1ff0000e3c 0x4103c01c02f00ef0

def z1562 : W := mkw 0x93a4042000004000 0xf60ffffdef000300 0xffffffe00e387fc3 0xfeffffffff010f0f

def z1563 : W := mkw 0x93a4000000000000 0x74033f99ec000000 0xffffc00000000000 0xfc0ffffffc000000

def z1564 : W := mkw 0x93a4000000000000 0xa40dff09ec000000 0xffffc00000000000 0xfc0fff3ffc000000

def z1565 : W := mkw 0x60488b0c86423210 0x09e0000210cccccc 0x03c03f1f8fc77e3b 0xbbe0000002eececc

def z1566 : W := mkw 0xdba42ebf65246920 0xf60ffffdeff45750 0xfffffffff007fffc 0xff4ffffffff0fff0

def z1567 : W := mkw 0x93a4000000000000 0x04000209ec000000 0xffffc00000000000 0x1c00003ffc000000

def z1568 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0xffffc01c00007038 0xff4ffffffc0000c0

def z1569 : W := mkw 0xdfa566b530096969 0xf60ffffdefb02772 0xfffffffff038fffc 0xff5ffffffff13ff3

def z1570 : W := mkw 0xd3a43ade4d242000 0xf60ffffdeff75440 0xfffffffffffffe38 0xffcffffffffffec0

def z1571 : W := mkw 0x020038da4d240000 0xa20dfd60a3775000 0x00073fffffff8000 0xe38fff2063fff000

def z1572 : W := mkw 0x025235f00a905482 0x820cd862a33b0b05 0x03ff3fe38ff87fc3 0xbaffb8e3e3ef0f0f

def z1573 : W := mkw 0x8380000000000000 0xf00f3ef9ec000000 0xffffc00000000000 0xfc0ffffffc000000

def z1574 : W := mkw 0x60489b4c8e423210 0x8bec180213cfcccc 0x00003fff8fff7e3b 0xa3ec380003efcecc

def z1575 : W := mkw 0x0a5235f12a905da2 0x820cd866a33b0b15 0x03ff3fe00ff87fc3 0xbafc38e3e30f0f0f

def z1576 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0xffffc0fc70000000 0xff0ffffffd100000

def z1577 : W := mkw 0x61488b0c86423210 0x79e3249314cccccc 0xe3ffff1f8fc77e3b 0xffefbcf3feeececc

def z1578 : W := mkw 0xca8026b520006920 0xd20edafcebb00750 0xfffffffff0007ffc 0xff4ffffffff00ff0

def z1579 : W := mkw 0x0a123cfb6db44da2 0xa20dfd64a3775311 0x1c073fffffff81c4 0xe39fff2c63fff133

def z1580 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0xe3ffc00000000000 0xfc0bbfd3fc000000

def z1581 : W := mkw 0x205a9d688ed25692 0x0be00002134fcb8d 0x00003fe00fff7fc3 0x02f00000030fcf0f

def z1582 : W := mkw 0x2048994acf661210 0x29e13d02104fd88c 0x000000000fff8003 0x20a03f00000ff00c

def z1583 : W := mkw 0x61488b0c86423210 0x79e3249314cccccc 0xfff8ff1f8fc77fff 0xffebb4ff9eeecffc

def z1584 : W := mkw 0x93a4209000000000 0xf60ffffdef300000 0xffffc0e070000000 0xfc0ffffffd100000

def z1585 : W := mkw 0x0312146008904482 0xf20f3cf1a7030301 0xe3ffc0e0003801c0 0xfc1fbcf3fd010103

def z1586 : W := mkw 0x0000080a45240000 0x2001250000445000 0x00003f1f8fc78000 0xe38bb70002eef000

def z1587 : W := mkw 0x00123cfa4db44482 0xa20dfd0003775301 0x00003fffffff81c0 0xe39fff0003fff103

def z1588 : W := mkw 0x0100000000000000 0xf00f3c9104000000 0xe3f8c00000000000 0xfc0fbcd39c000000

def z1589 : W := mkw 0x4a0026b520006920 0xd20ec0f4a3b00750 0xffff3ffff0007ffc 0xdb4fc0ffe3f00ff0

def z1590 : W := mkw 0x61488b0c86423210 0x79e3249314cccccc 0xe038ff1f81c77e38 0xd74bb4d39eeecec0

def z1591 : W := mkw 0x245355601a9954cb 0x0bc00002130babaf 0x00003fe00fffffc3 0x02f00000030fff0f

def z1592 : W := mkw 0x480036f769246920 0xd20ed9f403b31750 0xfc003ffffe3ffffc 0xf3cfcffc03f1fff0

def z1593 : W := mkw 0x0040010002001000 0x0000000200080804 0x03ff3f000fc07fc3 0xbaf830e3e20e0f0f

def z1594 : W := mkw 0x025235f24bb45482 0x820cd962a33b1b05 0x03ff3fe00ff87fc3 0xbafc38e3e30f0f0f

def z1595 : W := mkw 0x480026b520006920 0xd20ec0f403b00750 0xfc003ffff0007ffc 0xf34fcffc03f00ff0

def z1596 : W := mkw 0x0000080804000000 0x2001240000444000 0x00003f1fffc78000 0xe38bf70002fef000

def z1597 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0xffffff0000007e00 0xfe4ffffffe000e00

def z1598 : W := mkw 0x025215600a905482 0x820c1862a30b0b05 0x03ff3ffc0fff7fc3 0xfbfc3ce3e30fcf0f

def z1599 : W := mkw 0x93a4080804000000 0xf40ffffdec444000 0xffffff0381c00000 0xfc0ffffffeee0000

def z1600 : W := mkw 0x0300000000000000 0xf00ffdf1a4000000 0xe3ffc00000000000 0xfc0ffff3fc000000

def z1601 : W := mkw 0x4800062520006920 0xd00ec0f400800750 0xfc003f1f80007ffc 0xd34fc0fc02e00ff0

def z1602 : W := mkw 0x93a4104008000000 0xf60ffffdef030000 0xfffffffc7fff8000 0xff8fffffff1ff000

def z1603 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0xffffc01c7000003c 0xfd0ffffffc1000f0

def z1604 : W := mkw 0x93a4000000000000 0xa40dff6dec000000 0x03ffc00000000000 0x2c003f03fc000000

def z1605 : W := mkw 0x6048ab9c86423210 0x8becc00213fccccc 0x00003fffffc77e3b 0xc3efc00003fececc

def z1606 : W := mkw 0x0252010002901482 0x00000002a0080805 0x03ff3f000fc07e03 0xbaf830c3e20e0e0f

def z1607 : W := mkw 0xedc9c725b24b7b79 0x59e202ff5c88affe 0xffffc00000007fff 0x1c7000fffc000fff

def z1608 : W := mkw 0x60488b0c86423210 0x29e1240210cccccc 0x00003f1f8fc77e3b 0x03ebb00002eececc

def z1609 : W := mkw 0x2048810082421210 0x09e000021008888c 0x0000000000000003 0x002000000000000c

def z1610 : W := mkw 0x93a4184a4d240000 0xf40ffffdec475000 0xffffc00001c00000 0xfc0ffffffc0e0000

def z1611 : W := mkw 0x93a438da4d240000 0xf60fff99ef775000 0xe3ffffffffff8000 0xff8fffd3fffff000

def z1612 : W := mkw 0x1324000000000000 0x24013d01a4000000 0x03f8c00000000000 0x2c0034039c000000

def z1613 : W := mkw 0x93a4146008004000 0xf60ffffdef030300 0xffffffe00ff87fc0 0xfecfffffff0f0f00

def z1614 : W := mkw 0xdba426b520006920 0x560202fdefb00750 0xfffffffff0007ffc 0x1f4000fffff00ff0

def z1615 : W := mkw 0xdba4229520002920 0x5402c2fdecb00450 0xffffc01ff000003c 0x5d03c0fffcf000f0

def z1616 : W := mkw 0x93a4000000000000 0x24013f09ec000000 0x1fffc00000000000 0x2c047f2ffc000000

def z1617 : W := mkw 0x025215600a905482 0x02001862a30b0b05 0x03ff3fe00ff87fc3 0x3af038e3e30f0f0f

def z1618 : W := mkw 0x93a4080804000000 0xf40ffffdec444000 0xffffc0000fc70000 0xfc8ffffffc0ec000

def z1619 : W := mkw 0x4000020400002000 0x5002009000800440 0xfc003f1ff0007e3c 0xd34bc0dc02f00ef0

def z1620 : W := mkw 0x93a430d249240000 0xf60ffffdef331000 0xfffffffff0388000 0xff0ffffffff13000

def z1621 : W := mkw 0x645bdf6c9edb76db 0x0be0000213cfefef 0x00003fffffffffff 0x03f0000003ffffff

def z1622 : W := mkw 0x025235f00a905482 0x820c1862a33b0b05 0x03ff3ffffff87fc3 0xbbfc38e3e3ff0f0f

def z1623 : W := mkw 0x93a4209000000000 0xf60ffffdef300000 0xfffffffffe3f8000 0xff8ffffffff1f000

def z1624 : W := mkw 0x61488b0c86423210 0x79e3249314cccccc 0x03f8ff1f8fc70e03 0xefabb4c39eeece0c

def z1625 : W := mkw 0x000038da4d240000 0xa20dfd0003775000 0x00003fffffff8000 0x438bf70003fff000

def z1626 : W := mkw 0x61488b0c86423210 0x79e3249314cccccc 0x00003f1f8fc77e3b 0x03e3800002eececc

def z1627 : W := mkw 0x5b2426b520006920 0xf60ffdf5a7b00750 0xe3f8ff1f80007e38 0xff4bb4d39ee00ec0

def z1628 : W := mkw 0x6449cb0c964b3259 0x59e2009210ccecee 0xfc003fffffffffff 0xd3ffc0fc03ffffff

def z1629 : W := mkw 0x93a4000000000000 0x7403e7fdec000000 0xffffc00000000000 0xfc07cffffc000000

def z1630 : W := mkw 0x6848bfffef667b30 0xfbeffdf613ffdfdc 0xfc003fffffffffff 0xf3effffc03fffffc

def z1631 : W := mkw 0x93a4000000000000 0x74033ffdec000000 0x03ffc00000000000 0x2c003fc3fc000000

def z1632 : W := mkw 0x4000062400006000 0xd20e00f003800740 0xfc003ffff0007ffc 0xd34fc0fc03f00ff0

def z1633 : W := mkw 0xdba4062520006920 0x740326fdec800750 0xffffff1f80007ffc 0xff4bb4fffee00ff0

def z1634 : W := mkw 0x021238da4db40482 0xa20dfd00a3775001 0x00073fffffff8000 0xe39fff0063fff003

def z1635 : W := mkw 0x93a4184a4d240000 0x24013f09ec475000 0xffffc0fc7fff8000 0xff847f3ffd1ff000

def z1636 : W := mkw 0x93a4289a45240000 0xf40ffffdec745000 0xffffc00380000000 0xfc0ffffffce00000

def z1637 : W := mkw 0x2048890886421210 0x29e12402104cc88c 0x00003f1f8fc70003 0xe3abb40002eec00c

def z1638 : W := mkw 0x0100000000000000 0x7003e59104000000 0xe3f8c00000000000 0xfc0bf7d39c000000

def z1639 : W := mkw 0x025215600a905482 0x820c1862a30b0b05 0x03ff3fe07ff8ffc3 0xbafc7be3e31f3f0f

def z1640 : W := mkw 0x93a430d249240000 0xf60ffffdef331000 0xffffc0fc7e3f8000 0xff8ffffffd11f000

def z1641 : W := mkw 0x1324000000000000 0x740324f5a4000000 0xe3f8c00000000000 0xfc0bb4d39c000000

def z1642 : W := mkw 0x025235f24bb45482 0x820cd962a33b1b05 0x03ff3ffffff8ffc3 0xfbfffbe3e3ff3f0f

def z1643 : W := mkw 0x0100104008000000 0xf20f3c9107030000 0xe3f8ffe00ff80000 0xfe8fbcd39f0f0000

def z1644 : W := mkw 0x93a4000000000000 0x7403ff9dec000000 0xfc38c00000000000 0x4403f71f9c000000

def z1645 : W := mkw 0x480026b520006920 0xd20ec0f403b00750 0xfc003f1f80007ffc 0xd34b80fc02e00ff0

def z1646 : W := mkw 0x480026b520006920 0xd20ec0f403b00750 0xfc003f1ff0007e3c 0xd34bc0dc02f00ef0

def z1647 : W := mkw 0x8180080804000000 0x700326994c444000 0xffffffffffff8000 0xff8ffffffffff000

def z1648 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0xfff8c00000000000 0xfc0bf7df9c000000

def z1649 : W := mkw 0x000038da4d240000 0xa20dfd0003775000 0x1c003fffffff81c4 0xe38fff2c03fff130

def z1650 : W := mkw 0x93a4289a45240000 0x2401ff09ec745000 0x03ffc01ff0078000 0x6d03ff03fcf0f000

def z1651 : W := mkw 0x6848afbda6427b30 0x0be0000213fccfdc 0x00003f1f8fc77e3b 0x03e0000002eececc

def z1652 : W := mkw 0x4000020400002000 0xd00ec0f400800440 0xfc003ffff0007ffc 0xd34fc0fc03f00ff0

def z1653 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0xffffc000000071c3 0xfc7ffffffc00010f

def z1654 : W := mkw 0x025215600a905482 0x02000062a30b0b05 0x03ff3fe00ff87fc3 0xbaf830e3e30f0f0f

def z1655 : W := mkw 0x0100000000000000 0x7003249104000000 0xe3f8c00000000000 0x5c0384d39c000000

def z1656 : W := mkw 0x605a97648ad27692 0x0be00002138b8fcd 0x00003fe00ff87ffb 0x02f00000030f0fcf

def z1657 : W := mkw 0x9ba424b120004920 0xf60ffffdef300310 0xffffffe070007fc4 0xfe4fffffff100f30

def z1658 : W := mkw 0x97b75460189944cb 0xf60ffffdef032323 0xffffc0e0703881c4 0xfc1ffffffd113133

def z1659 : W := mkw 0x93a4000000000000 0x7403fffdec000000 0xffffc00000000000 0x7c03fffffc000000

def z1660 : W := mkw 0x93b6104008900482 0xf40ffffdec030001 0xffffc00000380000 0xfc1ffffffc010003

def z1661 : W := mkw 0x93a4000000000000 0x540202fdec000000 0xffffc000000071c3 0x1c7000fffc00010f

def z1662 : W := mkw 0x61488b0c86423210 0x79e3249314cccccc 0xfff8ffffffffffff 0xffefffff9ffffffc

def z1663 : W := mkw 0x6449c304924b3259 0x09e000021088acee 0x000000fc7e3fffff 0x03f000000111ffff

def z1664 : W := mkw 0x000038da4d240000 0xa20dfd6003775000 0x00003fffffff8000 0xf38fffe003fff000

def z1665 : W := mkw 0x4100020400002000 0x5002009104800440 0xe3f8ff1f80007e38 0xdf4b80d39ee00ec0

def z1666 : W := mkw 0x93a438da4d240000 0xf60ffffdef775000 0xfc38ffffffff8000 0xe78fffdf9ffff000

def z1667 : W := mkw 0x97a578da5d2d0049 0xf60ffffdef777022 0xffffffffffff81c4 0xff9ffffffffff133

def z1668 : W := mkw 0xdba43eff6d246920 0xf60ffffdeff75750 0xffffffffffff8e00 0xff8ffffffffffe00

def z1669 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0xffffc00000000000 0xbc0fb8fffc000000

def z1670 : W := mkw 0x93a4000000000000 0xf40ffffdec000000 0xffffc00000000000 0x6c0bffdffc000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z3,z7,z8,z6]),(0,[z0,z1,z2,z3,z9,z5,z6]),(1,[z0,z10,z2,z3,z11,z6]),(0,[z0,z1,z2,z12,z5,z6,z13]),(0,[z14,z0,z1,z2,z3,z5,z6]),(0,[z15,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z16,z2,z3,z5,z6])],[(0,[z0,z1,z17,z2,z3,z18,z6]),(1,[z0,z1,z2,z3,z19,z6]),(0,[z0,z1,z20,z2,z3,z6,z21]),(0,[z0,z1,z20,z2,z3,z22,z6]),(0,[z0,z23,z24,z1,z2,z3,z6]),(1,[z0,z1,z25,z3,z5,z6]),(0,[z0,z1,z2,z3,z22,z6,z26]),(0,[z0,z27,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z28,z5,z6]),(0,[z0,z1,z2,z3,z29,z5,z6]),(0,[z0,z1,z2,z3,z30,z6,z31]),(0,[z0,z1,z32,z2,z3,z5,z6]),(0,[z0,z24,z33,z1,z2,z3,z6]),(0,[z0,z1,z34,z2,z3,z5,z26])],[(0,[z35,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z36,z3,z6,z37]),(0,[z0,z1,z2,z38,z3,z6,z37]),(0,[z0,z1,z2,z3,z22,z22,z6]),(0,[z0,z1,z39,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z40]),(0,[z41,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z42,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z43,z5,z6]),(0,[z0,z24,z1,z2,z5,z6,z26])],[(0,[z0,z1,z44,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z45,z5,z6]),(0,[z46,z0,z1,z2,z3,z5,z6]),(0,[z47,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z48,z2,z3,z22,z6]),(0,[z49,z0,z24,z1,z2,z3,z6]),(0,[z50,z0,z1,z2,z51,z3,z6]),(0,[z0,z1,z2,z3,z52,z5,z6])],[(0,[z0,z53,z1,z2,z3,z22,z6]),(1,[z0,z1,z2,z3,z54,z6]),(0,[z0,z1,z55,z2,z3,z6,z37]),(0,[z56,z0,z1,z2,z57,z5,z6])],[(0,[z0,z1,z2,z3,z58,z5,z6]),(0,[z59,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z60,z51,z3,z6]),(0,[z0,z1,z61,z2,z3,z5,z6]),(0,[z62,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z63,z6]),(1,[z64,z1,z2,z3,z5,z6]),(0,[z0,z65,z1,z2,z51,z3,z6]),(0,[z0,z1,z2,z3,z66,z5,z6])],[(0,[z59,z0,z1,z2,z3,z18,z6]),(0,[z0,z1,z2,z3,z6,z37,z67]),(0,[z0,z1,z2,z51,z3,z68,z6]),(0,[z0,z1,z34,z2,z12,z5,z6])],[(0,[z0,z1,z2,z3,z69,z5,z6]),(0,[z70,z0,z23,z2,z3,z5,z6]),(0,[z0,z1,z71,z3,z5,z68,z6])],[(0,[z0,z72,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z73,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z74])],[(0,[z50,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z75]),(0,[z76,z0,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z3,z77,z5,z6]),(0,[z56,z0,z1,z2,z3,z43,z6]),(0,[z0,z1,z2,z3,z5,z6,z78]),(0,[z0,z1,z2,z3,z79,z5,z80])],[(0,[z81,z0,z1,z2,z51,z3,z6]),(0,[z0,z1,z2,z3,z5,z82,z6]),(1,[z0,z1,z83,z3,z5,z6])],[(0,[z84,z0,z1,z2,z3,z6,z37]),(0,[z50,z0,z1,z2,z3,z18,z6]),(0,[z85,z0,z1,z86,z3,z5,z6]),(0,[z0,z1,z2,z60,z3,z5,z6]),(0,[z87,z0,z1,z2,z3,z5,z6]),(0,[z0,z88,z24,z1,z2,z3,z6]),(0,[z0,z24,z1,z2,z3,z3,z6])],[(0,[z0,z1,z89,z2,z3,z5,z6]),(0,[z90,z91,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z92]),(0,[z81,z0,z1,z2,z3,z93,z6]),(0,[z0,z1,z2,z94,z3,z5,z6]),(0,[z0,z1,z95,z2,z3,z5,z6]),(0,[z0,z23,z96,z2,z3,z5,z6]),(0,[z0,z65,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z97,z6]),(0,[z0,z1,z2,z3,z98,z5,z6]),(0,[z0,z24,z1,z2,z3,z99,z6]),(0,[z0,z1,z2,z3,z5,z6,z100]),(0,[z0,z1,z101,z2,z3,z5,z6])]],
   [[(0,[z0,z96,z102,z2,z3,z5,z6]),(0,[z103,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z7,z6,z75]),(1,[z0,z1,z2,z104,z5,z6]),(0,[z0,z1,z105,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z106])],[(0,[z0,z1,z2,z107,z3,z5,z6]),(0,[z0,z1,z2,z108,z3,z5,z6]),(0,[z0,z1,z2,z3,z22,z68,z6])],[(0,[z109,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z18,z6,z31]),(0,[z0,z110,z24,z1,z2,z3,z6]),(0,[z0,z1,z44,z2,z3,z99,z5]),(0,[z1,z2,z3,z5,z6,z111,z26])],[(0,[z112,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z7,z97,z6]),(0,[z0,z1,z2,z3,z18,z6,z113]),(0,[z76,z0,z1,z2,z3,z5,z8]),(0,[z0,z1,z20,z2,z3,z114,z6]),(0,[z0,z1,z2,z25,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z115,z6]),(0,[z0,z1,z116,z2,z3,z6,z37]),(0,[z0,z1,z71,z2,z3,z5,z117]),(0,[z0,z1,z118,z2,z3,z5,z6])],[(0,[z119,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z120]),(0,[z81,z0,z1,z2,z3,z5,z6]),(0,[z121,z0,z1,z2,z3,z22,z6]),(0,[z70,z0,z2,z122,z3,z5,z6]),(0,[z0,z1,z123,z2,z3,z5,z6]),(0,[z0,z1,z124,z2,z3,z6,z37]),(0,[z0,z125,z1,z2,z3,z5,z6]),(0,[z0,z1,z126,z2,z3,z5,z6])],[(0,[z127,z0,z1,z2,z3,z128,z6]),(0,[z0,z1,z2,z3,z5,z129,z6]),(0,[z0,z1,z130,z131,z3,z5,z6]),(0,[z0,z1,z2,z132,z3,z5,z6]),(0,[z0,z1,z2,z133,z3,z5,z6]),(0,[z134,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z135,z2,z51,z3,z6]),(0,[z0,z1,z136,z2,z51,z3,z6])],[(0,[z137,z76,z1,z2,z3,z5,z6]),(0,[z81,z0,z1,z2,z3,z18,z6]),(1,[z0,z1,z2,z3,z138,z6]),(0,[z0,z1,z139,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z22,z140,z6]),(0,[z0,z1,z2,z3,z5,z6,z111])],[(0,[z109,z0,z24,z1,z2,z3,z6]),(0,[z0,z1,z20,z2,z3,z7,z6]),(0,[z0,z2,z141,z3,z5,z6,z31]),(0,[z0,z96,z1,z2,z3,z6,z37]),(0,[z142,z0,z1,z2,z3,z6,z37]),(0,[z0,z1,z2,z57,z3,z5,z6]),(0,[z0,z1,z71,z2,z3,z6,z143])]],
   [[(0,[z144,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z145,z2,z3,z5,z6]),(0,[z91,z76,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z146]),(0,[z121,z147,z1,z2,z3,z5,z6]),(0,[z0,z148,z1,z149,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z150]),(0,[z56,z0,z1,z130,z3,z5,z6]),(0,[z0,z1,z151,z2,z3,z22,z6]),(0,[z0,z1,z71,z2,z3,z152,z6])],[(0,[z1,z102,z2,z153,z3,z5,z6]),(0,[z0,z1,z2,z3,z22,z7,z6]),(0,[z0,z1,z154,z2,z3,z5,z6]),(0,[z0,z24,z1,z136,z2,z3,z6]),(1,[z0,z1,z155,z3,z5,z6])],[(1,[z0,z156,z2,z3,z5,z6]),(0,[z0,z157,z1,z2,z3,z5,z6]),(0,[z158,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z159,z5,z6]),(0,[z0,z1,z2,z3,z5,z160,z6]),(0,[z0,z1,z2,z3,z161,z22,z6]),(0,[z162,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z12,z5,z6,z26])],[(0,[z0,z23,z102,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z163,z6]),(0,[z0,z1,z48,z2,z3,z7,z6]),(0,[z164,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z165,z5,z6]),(0,[z0,z1,z124,z48,z3,z5,z6]),(1,[z0,z166,z2,z3,z5,z6]),(0,[z0,z1,z167,z2,z3,z5,z6])],[(0,[z127,z1,z102,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z168,z5,z6]),(0,[z169,z0,z1,z2,z3,z5,z6]),(0,[z170,z0,z1,z2,z3,z5,z6]),(0,[z158,z0,z1,z2,z3,z18,z6]),(0,[z0,z1,z171,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z172,z6]),(0,[z0,z173,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z174,z5,z6]),(0,[z0,z2,z3,z5,z97,z6,z31]),(0,[z175,z0,z1,z2,z3,z5,z6]),(0,[z56,z64,z1,z2,z3,z5,z6]),(0,[z0,z1,z135,z2,z3,z5,z6]),(0,[z0,z1,z136,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z176,z5,z6]),(0,[z0,z1,z2,z51,z3,z177,z6]),(0,[z0,z1,z2,z3,z165,z18,z6]),(0,[z0,z1,z2,z3,z5,z6,z178]),(0,[z0,z1,z34,z2,z51,z3,z6])],[(0,[z0,z179,z1,z2,z3,z5,z6]),(1,[z0,z180,z1,z2,z3,z6]),(0,[z181,z0,z1,z2,z3,z6,z37]),(0,[z0,z1,z171,z2,z3,z18,z6]),(0,[z0,z1,z2,z3,z174,z18,z6]),(0,[z0,z1,z136,z2,z3,z18,z6]),(0,[z0,z1,z182,z2,z3,z5,z6]),(0,[z0,z1,z141,z3,z5,z6,z37]),(0,[z0,z1,z2,z3,z183,z5,z6]),(0,[z0,z1,z2,z3,z5,z184,z6]),(0,[z70,z0,z1,z2,z3,z5,z31]),(0,[z185,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z130,z20,z3,z5,z6]),(0,[z70,z0,z1,z2,z3,z22,z6]),(0,[z0,z1,z130,z2,z3,z6,z37]),(0,[z186,z0,z24,z1,z2,z3,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z187,z6]),(0,[z90,z0,z1,z2,z177,z5,z6]),(0,[z90,z1,z2,z3,z177,z5,z6]),(0,[z188,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z189,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z18,z190,z6])],[(0,[z90,z1,z2,z153,z3,z5,z6]),(0,[z0,z191,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z51,z3,z6])],[(0,[z192,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z153,z51,z3,z6]),(0,[z76,z0,z1,z2,z3,z7,z6]),(0,[z85,z0,z1,z2,z3,z22,z6]),(0,[z0,z193,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z141,z51,z3,z6]),(0,[z194,z0,z1,z2,z3,z5,z6]),(0,[z0,z23,z1,z2,z3,z6,z37]),(1,[z0,z1,z195,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z196,z6]),(0,[z0,z1,z2,z3,z5,z6,z197]),(0,[z0,z1,z2,z3,z99,z6,z37]),(0,[z0,z24,z125,z1,z2,z3,z6])],[(1,[z0,z1,z2,z3,z93,z6]),(0,[z0,z1,z2,z3,z5,z6,z67]),(0,[z198,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z199,z3,z6]),(0,[z0,z1,z2,z3,z5,z6,z200])],[(0,[z0,z1,z201,z2,z3,z5,z6]),(0,[z0,z124,z202,z2,z3,z5,z6]),(0,[z0,z1,z71,z2,z3,z6,z37]),(0,[z0,z1,z2,z3,z79,z22,z6]),(0,[z0,z1,z2,z203,z3,z5,z6]),(0,[z0,z1,z2,z3,z204,z5,z6]),(0,[z0,z1,z34,z2,z3,z5,z6]),(1,[z0,z1,z44,z2,z5,z26])],[(0,[z1,z102,z2,z36,z3,z5,z6]),(1,[z0,z1,z2,z3,z205,z6]),(0,[z0,z1,z2,z3,z206,z5,z6]),(0,[z0,z24,z1,z2,z3,z11,z6]),(0,[z0,z1,z130,z3,z161,z5,z6])],[(0,[z0,z1,z34,z2,z3,z18,z6]),(0,[z0,z1,z2,z3,z12,z5,z6])],[(1,[z0,z1,z2,z3,z207,z6]),(1,[z0,z1,z2,z3,z208,z6]),(0,[z0,z1,z2,z3,z5,z19,z6]),(0,[z76,z0,z24,z1,z2,z3,z6]),(0,[z0,z1,z209,z2,z3,z5,z6]),(0,[z0,z1,z2,z210,z3,z5,z6]),(0,[z0,z1,z2,z51,z3,z11,z6]),(0,[z0,z1,z48,z3,z5,z68,z6])]],
   [[(1,[z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z153,z3,z208,z6]),(0,[z0,z1,z2,z3,z12,z18,z6]),(1,[z0,z1,z141,z3,z6,z37]),(0,[z0,z211,z1,z2,z3,z5,z6]),(0,[z0,z148,z1,z2,z3,z212,z6]),(1,[z70,z0,z2,z3,z5,z31]),(0,[z0,z1,z213,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z214,z6,z26])],[(0,[z0,z1,z2,z153,z3,z5,z6]),(0,[z85,z0,z1,z2,z3,z5,z8]),(0,[z0,z1,z2,z3,z172,z5,z6]),(0,[z0,z1,z2,z141,z3,z5,z6]),(0,[z215,z0,z1,z2,z51,z3,z6]),(0,[z0,z1,z61,z2,z3,z99,z6])],[(0,[z0,z1,z1,z2,z3,z5,z6]),(0,[z216,z1,z102,z2,z3,z5,z6]),(0,[z76,z1,z102,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z6,z217]),(1,[z0,z1,z2,z3,z18,z6]),(0,[z121,z0,z1,z2,z3,z7,z6]),(0,[z0,z53,z1,z2,z3,z174,z6]),(0,[z0,z1,z2,z3,z5,z6,z218]),(0,[z0,z1,z2,z3,z5,z6,z219])],[(0,[z0,z1,z2,z153,z3,z18,z6]),(0,[z0,z1,z2,z141,z3,z18,z6]),(0,[z70,z0,z2,z3,z5,z6,z31]),(0,[z0,z1,z2,z3,z5,z6,z220]),(0,[z0,z1,z2,z3,z6,z37,z221])],[(0,[z0,z1,z222,z2,z3,z5,z6]),(0,[z0,z216,z96,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z223]),(0,[z0,z24,z1,z2,z122,z3,z6]),(0,[z0,z1,z2,z3,z5,z54,z6]),(0,[z0,z24,z1,z44,z2,z3,z6]),(0,[z0,z1,z2,z3,z224,z5,z6])],[(0,[z0,z216,z2,z141,z3,z5,z6]),(0,[z0,z1,z225,z2,z3,z5,z6]),(1,[z0,z1,z55,z2,z3,z6])],[(0,[z0,z1,z151,z2,z3,z7,z6]),(0,[z0,z23,z1,z2,z165,z5,z6]),(0,[z0,z1,z2,z51,z122,z3,z6]),(0,[z0,z1,z202,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z6,z226]),(0,[z227,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z228]),(1,[z0,z1,z2,z3,z229,z6]),(0,[z121,z0,z24,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z22,z11,z6]),(0,[z0,z230,z1,z2,z3,z5,z31]),(0,[z0,z1,z231,z2,z3,z6,z37])]],
   [[(0,[z0,z1,z2,z232,z3,z5,z6]),(0,[z137,z0,z1,z2,z3,z22,z6]),(0,[z0,z1,z233,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z234,z6]),(0,[z215,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z161,z7,z6]),(0,[z0,z1,z2,z3,z7,z6,z223]),(1,[z235,z1,z2,z3,z5,z6]),(0,[z0,z230,z1,z2,z3,z22,z6]),(0,[z0,z1,z124,z48,z2,z5,z6]),(0,[z0,z1,z236,z2,z3,z5,z6]),(0,[z0,z1,z237,z2,z3,z5,z6])],[(0,[z0,z238,z1,z2,z3,z5,z6])],[(0,[z239,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z129,z6]),(0,[z91,z0,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z3,z5,z240,z6]),(0,[z0,z1,z44,z2,z3,z22,z6])],[(0,[z0,z1,z241,z2,z3,z5,z6]),(0,[z0,z1,z242,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z243]),(0,[z0,z1,z2,z3,z244,z5,z6]),(0,[z0,z1,z2,z3,z6,z37,z245]),(0,[z0,z1,z2,z3,z246,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z247])],[(0,[z0,z1,z2,z3,z177,z22,z6]),(0,[z0,z1,z2,z3,z5,z6,z248]),(1,[z0,z1,z2,z3,z6,z21]),(0,[z0,z1,z2,z3,z249,z5,z6]),(0,[z0,z24,z1,z2,z3,z250,z6])],[(0,[z127,z0,z1,z251,z3,z5,z6]),(0,[z0,z1,z2,z36,z3,z5,z6]),(0,[z70,z0,z1,z2,z3,z7,z6]),(1,[z84,z1,z2,z3,z18,z6]),(1,[z252,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z253]),(0,[z0,z1,z2,z38,z3,z5,z6]),(1,[z0,z1,z2,z57,z5,z6])],[(0,[z0,z1,z2,z3,z5,z254,z6]),(0,[z0,z1,z255,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z256,z6]),(0,[z0,z1,z257,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z258,z6]),(0,[z0,z1,z2,z3,z5,z6,z259])],[(0,[z127,z0,z1,z222,z3,z5,z6]),(0,[z0,z1,z48,z131,z3,z5,z6]),(0,[z90,z1,z2,z3,z5,z8,z6]),(0,[z0,z1,z2,z36,z3,z18,z6]),(0,[z121,z260,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z160,z6]),(0,[z0,z261,z1,z2,z3,z5,z6]),(0,[z0,z1,z34,z2,z99,z5,z6])]],
   [[(0,[z85,z0,z1,z2,z3,z7,z6]),(0,[z85,z0,z262,z2,z3,z5,z6]),(1,[z147,z1,z2,z3,z5,z6]),(0,[z0,z263,z1,z2,z3,z5,z6]),(0,[z0,z1,z55,z2,z3,z5,z6])],[(0,[z264,z0,z1,z2,z3,z5,z6]),(0,[z84,z0,z1,z2,z51,z3,z6]),(0,[z0,z1,z141,z3,z5,z6,z117]),(0,[z0,z23,z2,z3,z5,z97,z6]),(0,[z0,z1,z2,z265,z3,z5,z6]),(1,[z0,z1,z2,z266,z5,z6]),(0,[z0,z1,z2,z161,z5,z6,z26]),(0,[z0,z1,z2,z3,z5,z6,z267]),(0,[z56,z0,z1,z3,z5,z6,z117])],[(0,[z0,z1,z2,z3,z79,z7,z6]),(1,[z0,z1,z2,z268,z5,z6]),(0,[z70,z0,z24,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z269,z5,z6])],[(0,[z0,z1,z2,z3,z270,z5,z6]),(0,[z252,z0,z1,z2,z3,z5,z6]),(0,[z0,z10,z1,z2,z3,z6,z37]),(0,[z0,z1,z271,z2,z3,z5,z6])],[(0,[z0,z180,z1,z2,z3,z5,z6]),(1,[z0,z23,z2,z165,z5,z6]),(0,[z0,z1,z2,z122,z3,z6,z37]),(0,[z0,z24,z1,z2,z3,z22,z6])],[(0,[z85,z0,z24,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z6,z31,z37])],[(0,[z0,z1,z153,z141,z3,z5,z6]),(0,[z91,z0,z1,z2,z3,z272,z6]),(0,[z56,z0,z1,z2,z3,z18,z6]),(0,[z1,z2,z3,z5,z8,z6,z75]),(0,[z121,z0,z1,z2,z3,z273,z6]),(0,[z0,z1,z2,z3,z6,z37,z26]),(0,[z0,z1,z2,z51,z3,z22,z6]),(0,[z0,z1,z274,z2,z51,z3,z6]),(0,[z0,z1,z116,z2,z51,z3,z6]),(0,[z0,z1,z2,z3,z5,z6,z275])],[(0,[z0,z102,z2,z122,z3,z5,z6]),(0,[z0,z216,z1,z2,z3,z6,z37]),(0,[z109,z0,z1,z2,z3,z22,z6]),(0,[z0,z24,z1,z2,z153,z3,z6]),(0,[z0,z1,z276,z2,z3,z5,z6]),(0,[z0,z2,z122,z3,z5,z97,z6]),(0,[z0,z1,z124,z2,z51,z3,z6])]],
   [[(0,[z0,z1,z102,z2,z3,z22,z6]),(0,[z0,z1,z130,z153,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z277,z6]),(0,[z84,z0,z1,z2,z3,z5,z6]),(0,[z278,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z265,z3,z165,z6])],[(0,[z127,z0,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z3,z3,z5,z6]),(0,[z0,z1,z48,z2,z3,z6,z37]),(0,[z279,z0,z1,z2,z3,z5,z6])],[(0,[z109,z0,z1,z2,z3,z280,z6]),(1,[z0,z1,z2,z3,z281,z6]),(0,[z84,z0,z1,z2,z3,z18,z6]),(1,[z0,z1,z107,z3,z5,z6]),(0,[z0,z96,z1,z2,z51,z3,z6]),(0,[z0,z148,z1,z2,z3,z29,z6]),(0,[z0,z53,z1,z2,z3,z6,z37])],[(0,[z0,z282,z1,z2,z3,z5,z6]),(0,[z137,z1,z2,z153,z3,z5,z6]),(0,[z81,z0,z1,z283,z3,z5,z6]),(1,[z0,z284,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z285,z5,z6]),(1,[z0,z1,z2,z3,z286,z6])],[(0,[z0,z1,z287,z2,z3,z5,z6]),(0,[z0,z23,z2,z3,z165,z5,z6]),(0,[z288,z0,z1,z2,z3,z5,z6]),(0,[z0,z289,z1,z2,z3,z5,z6]),(0,[z0,z1,z274,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z221]),(0,[z0,z1,z116,z2,z3,z5,z6])],[(0,[z0,z1,z2,z290,z3,z5,z6]),(0,[z137,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z5,z291,z6]),(0,[z0,z230,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z18,z8,z6]),(0,[z0,z1,z2,z3,z285,z18,z6]),(1,[z0,z1,z133,z3,z5,z6]),(0,[z292,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z2,z3,z22,z6])],[(0,[z293,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z294,z5,z6]),(0,[z0,z295,z1,z2,z3,z5,z6]),(0,[z296,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z48,z3,z161,z5,z6]),(0,[z0,z1,z2,z3,z297,z5,z6]),(0,[z298,z0,z1,z2,z3,z5,z6]),(0,[z0,z24,z1,z2,z3,z6,z299]),(0,[z0,z1,z2,z300,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z301])]],
   [[(0,[z91,z0,z1,z2,z3,z7,z6])],[(0,[z142,z0,z1,z2,z3,z5,z6]),(0,[z181,z0,z1,z2,z51,z3,z6]),(0,[z0,z1,z302,z2,z3,z5,z6]),(0,[z0,z96,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z303,z6,z37]),(1,[z56,z0,z1,z3,z5,z117]),(0,[z304,z0,z1,z2,z3,z5,z6])],[(0,[z305,z0,z1,z2,z3,z5,z6]),(0,[z109,z0,z306,z2,z3,z5,z6]),(0,[z1,z2,z153,z3,z5,z6,z75]),(0,[z90,z0,z1,z2,z3,z6,z37]),(0,[z0,z1,z2,z3,z177,z7,z6]),(0,[z0,z1,z130,z2,z51,z3,z6]),(0,[z0,z1,z2,z3,z5,z307,z6]),(0,[z56,z0,z1,z2,z3,z5,z68]),(0,[z0,z24,z1,z2,z3,z68,z6])],[(0,[z308,z0,z1,z2,z3,z5,z6]),(0,[z137,z0,z24,z1,z2,z3,z6]),(0,[z85,z76,z1,z2,z3,z5,z6]),(0,[z0,z2,z122,z3,z165,z5,z6]),(0,[z0,z24,z10,z1,z2,z3,z6]),(0,[z0,z309,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z310,z3,z5,z6])],[(0,[z0,z1,z153,z3,z5,z6,z117]),(0,[z0,z1,z311,z2,z3,z5,z6]),(0,[z0,z1,z2,z36,z5,z6,z26]),(0,[z0,z1,z2,z3,z312,z5,z6]),(0,[z0,z1,z313,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z314])],[(0,[z0,z1,z2,z3,z5,z207,z6]),(0,[z91,z0,z24,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z5,z6,z315]),(0,[z0,z23,z1,z2,z51,z3,z6]),(0,[z0,z316,z1,z2,z3,z5,z6]),(0,[z0,z1,z317,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z318,z5,z6]),(0,[z0,z319,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z5,z6]),(0,[z288,z148,z1,z2,z3,z5,z6]),(0,[z320,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z321,z3,z5,z6]),(0,[z0,z24,z1,z322,z2,z3,z6]),(1,[z0,z1,z61,z2,z3,z6])],[(0,[z323,z0,z1,z2,z3,z5,z6]),(0,[z76,z0,z1,z2,z3,z5,z75]),(0,[z0,z1,z2,z324,z3,z5,z6]),(0,[z0,z1,z71,z2,z51,z3,z6]),(0,[z0,z1,z136,z116,z2,z3,z5])]],
   [[(0,[z91,z1,z102,z2,z3,z5,z6]),(0,[z91,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z5,z6,z217]),(0,[z0,z1,z131,z71,z3,z5,z6]),(0,[z181,z0,z1,z2,z3,z5,z6]),(0,[z0,z325,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z114,z5,z6]),(0,[z0,z10,z1,z116,z2,z3,z6]),(0,[z0,z1,z2,z326,z3,z5,z6]),(0,[z0,z284,z1,z2,z3,z5,z6]),(0,[z0,z327,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z328,z3,z5,z6]),(0,[z0,z329,z1,z2,z3,z5,z6]),(0,[z330,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z34,z2,z36,z5,z6]),(0,[z0,z1,z2,z3,z7,z6,z245]),(0,[z0,z1,z130,z2,z3,z5,z6]),(0,[z0,z331,z1,z2,z3,z5,z6]),(0,[z0,z1,z32,z2,z3,z22,z6])],[(0,[z109,z1,z2,z153,z3,z5,z6]),(0,[z181,z0,z1,z2,z3,z18,z6]),(0,[z0,z24,z1,z2,z3,z7,z6]),(1,[z0,z1,z2,z332,z5,z6]),(0,[z0,z20,z2,z141,z3,z5,z6]),(0,[z0,z1,z333,z2,z3,z5,z6]),(0,[z334,z0,z1,z2,z3,z5,z6]),(0,[z0,z10,z1,z83,z3,z5,z6]),(0,[z0,z1,z335,z2,z3,z5,z6]),(0,[z0,z1,z2,z51,z3,z6,z80])],[(0,[z0,z1,z130,z2,z3,z18,z6]),(0,[z0,z23,z2,z141,z3,z5,z6]),(0,[z0,z1,z2,z3,z336,z5,z6]),(0,[z0,z1,z136,z2,z3,z5,z80])],[(0,[z0,z1,z337,z2,z3,z5,z6]),(0,[z0,z1,z338,z2,z3,z5,z6]),(0,[z0,z1,z2,z51,z3,z7,z6]),(0,[z84,z1,z2,z3,z18,z5,z6]),(1,[z1,z339,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z226]),(0,[z0,z1,z2,z3,z99,z5,z6])],[(0,[z340,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z341]),(0,[z0,z1,z2,z3,z342,z5,z6]),(0,[z0,z1,z195,z2,z3,z5,z6]),(0,[z343,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z102,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z5,z344,z6]),(0,[z0,z1,z2,z3,z18,z6,z75]),(0,[z0,z1,z2,z3,z99,z18,z6]),(0,[z0,z1,z2,z3,z345,z5,z6]),(0,[z59,z0,z1,z2,z3,z22,z6]),(0,[z0,z1,z71,z2,z3,z5,z6])],[(0,[z127,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z5,z6,z346]),(1,[z0,z1,z283,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z347,z6]),(0,[z0,z1,z83,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z348,z5,z6]),(0,[z0,z53,z1,z116,z2,z3,z6]),(0,[z0,z24,z24,z1,z2,z3,z6]),(0,[z349,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z350,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z351,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z26])],[(0,[z0,z1,z2,z3,z18,z97,z6]),(0,[z0,z352,z1,z2,z3,z5,z6]),(0,[z353,z0,z1,z2,z51,z3,z6])],[(0,[z354,z0,z1,z2,z3,z5,z6]),(0,[z355,z0,z1,z2,z3,z5,z6]),(0,[z0,z96,z1,z20,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z21]),(0,[z0,z356,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z22,z6,z80]),(0,[z0,z1,z116,z2,z3,z79,z5])],[(0,[z0,z23,z216,z2,z3,z5,z6]),(0,[z85,z1,z2,z3,z5,z6,z75]),(0,[z0,z148,z1,z2,z3,z6,z37]),(1,[z0,z1,z2,z3,z357,z6])],[(0,[z127,z0,z24,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z7,z6,z26]),(0,[z0,z1,z2,z3,z5,z358,z6]),(0,[z0,z1,z2,z3,z357,z5,z6]),(0,[z0,z359,z2,z3,z5,z6,z26]),(0,[z0,z1,z2,z3,z360,z5,z6])],[(0,[z0,z1,z131,z20,z3,z5,z6]),(0,[z0,z1,z131,z2,z3,z6,z37]),(1,[z0,z125,z1,z2,z3,z6]),(0,[z0,z1,z44,z34,z2,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z361])],[(0,[z0,z24,z1,z102,z2,z3,z6]),(0,[z362,z0,z1,z2,z3,z5,z6]),(0,[z0,z24,z1,z2,z3,z177,z6]),(0,[z0,z1,z2,z3,z8,z6,z37]),(1,[z0,z1,z363,z2,z3,z6]),(0,[z364,z0,z1,z2,z3,z5,z6]),(1,[z0,z24,z1,z2,z51,z6])],[(0,[z0,z1,z2,z3,z205,z5,z6]),(0,[z0,z1,z2,z365,z3,z5,z6]),(0,[z81,z0,z1,z2,z3,z344,z6]),(0,[z85,z0,z1,z2,z3,z366,z6]),(0,[z0,z1,z367,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z68,z6,z37]),(0,[z368,z0,z24,z1,z2,z3,z6])]],
   [[(0,[z0,z369,z1,z2,z3,z5,z6]),(0,[z0,z24,z1,z2,z3,z174,z6]),(0,[z0,z1,z2,z370,z3,z5,z6]),(0,[z353,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z371,z6]),(1,[z121,z0,z141,z3,z5,z6]),(0,[z0,z1,z372,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z6,z80,z37]),(0,[z0,z1,z231,z2,z3,z5,z6]),(1,[z0,z24,z1,z2,z6,z13]),(0,[z0,z1,z2,z3,z5,z6,z373])],[(0,[z76,z1,z2,z153,z3,z5,z6]),(0,[z0,z1,z2,z51,z3,z174,z6]),(0,[z0,z1,z2,z374,z51,z3,z6])],[(0,[z81,z0,z1,z2,z3,z22,z6]),(1,[z0,z1,z86,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z375,z6]),(0,[z0,z1,z2,z3,z11,z6,z37]),(0,[z0,z1,z2,z3,z5,z6,z376])],[(0,[z91,z0,z1,z131,z3,z5,z6]),(1,[z377,z1,z2,z3,z5,z6]),(0,[z0,z64,z1,z2,z3,z5,z6])],[(0,[z137,z0,z102,z2,z3,z5,z6]),(0,[z0,z230,z102,z2,z3,z5,z6]),(0,[z0,z1,z2,z378,z3,z5,z6]),(0,[z85,z0,z1,z2,z3,z5,z75]),(0,[z0,z110,z1,z2,z3,z5,z6]),(0,[z0,z1,z124,z130,z3,z5,z6])],[(0,[z0,z1,z2,z3,z18,z6,z37]),(0,[z0,z1,z2,z3,z5,z6,z379]),(0,[z0,z10,z1,z2,z51,z3,z6]),(0,[z0,z53,z2,z3,z174,z5,z6]),(0,[z0,z380,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z381,z5,z6]),(0,[z0,z382,z1,z2,z3,z5,z6]),(0,[z0,z1,z383,z2,z3,z5,z6])],[(0,[z0,z216,z230,z2,z3,z5,z6]),(0,[z0,z384,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z385,z3,z5,z6]),(0,[z0,z148,z1,z2,z165,z5,z6]),(0,[z252,z10,z1,z2,z3,z5,z6]),(0,[z0,z24,z1,z2,z3,z6,z31]),(0,[z0,z1,z124,z2,z3,z54,z6]),(0,[z0,z1,z386,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z281,z6]),(0,[z0,z387,z1,z2,z3,z5,z6])],[(0,[z137,z1,z2,z3,z5,z6,z75]),(0,[z0,z388,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z374,z3,z5,z6]),(0,[z0,z384,z1,z2,z3,z18,z6]),(0,[z0,z1,z389,z2,z3,z5,z6]),(0,[z0,z1,z2,z51,z3,z6,z31])],[(0,[z0,z216,z1,z2,z51,z3,z6]),(1,[z0,z1,z2,z3,z6,z245]),(0,[z0,z1,z2,z3,z165,z22,z6])],[(0,[z0,z390,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z153,z3,z6,z245]),(0,[z91,z1,z2,z3,z5,z6,z75]),(0,[z0,z1,z2,z3,z5,z391,z6]),(0,[z0,z1,z2,z3,z174,z22,z6]),(0,[z0,z24,z1,z124,z2,z3,z6]),(0,[z0,z1,z136,z2,z3,z22,z6]),(0,[z0,z1,z2,z51,z3,z66,z6])],[(0,[z137,z0,z1,z2,z3,z6,z37]),(0,[z0,z1,z2,z3,z392,z5,z6]),(0,[z0,z1,z2,z3,z7,z68,z6]),(0,[z59,z0,z1,z2,z3,z7,z6]),(0,[z0,z284,z124,z2,z3,z5,z6]),(0,[z0,z1,z2,z393,z3,z5,z6])],[(0,[z394,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z365,z3,z6]),(0,[z0,z1,z2,z3,z395,z7,z6]),(0,[z0,z10,z1,z2,z3,z5,z6]),(0,[z0,z53,z1,z2,z51,z3,z6]),(0,[z0,z1,z130,z2,z3,z286,z6]),(0,[z0,z1,z2,z3,z5,z140,z6])],[(0,[z0,z1,z2,z3,z5,z396,z6]),(0,[z91,z0,z1,z2,z3,z6,z37]),(0,[z0,z1,z397,z2,z3,z5,z6]),(0,[z398,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z122,z3,z5,z6]),(0,[z0,z1,z44,z2,z3,z6,z37])],[(0,[z0,z399,z1,z2,z3,z5,z6]),(0,[z0,z10,z1,z2,z3,z18,z6]),(0,[z0,z1,z2,z400,z3,z5,z6]),(0,[z46,z0,z24,z1,z2,z3,z6]),(0,[z0,z24,z1,z2,z3,z79,z6])]],
   [[(0,[z0,z1,z2,z122,z3,z18,z6]),(0,[z0,z401,z1,z2,z3,z5,z6]),(0,[z402,z0,z1,z2,z3,z5,z6])],[(0,[z0,z216,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z128,z6]),(0,[z109,z0,z1,z131,z3,z5,z6]),(0,[z0,z1,z2,z403,z3,z5,z6]),(0,[z50,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z22,z6,z31]),(0,[z0,z404,z1,z2,z3,z5,z6]),(0,[z59,z0,z24,z1,z2,z3,z6]),(0,[z0,z1,z2,z51,z3,z79,z6]),(0,[z0,z359,z1,z2,z3,z5,z6])],[(0,[z405,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z406,z5,z6])],[(0,[z0,z1,z2,z407,z3,z5,z6]),(0,[z0,z216,z1,z2,z3,z18,z6]),(0,[z1,z2,z153,z36,z3,z5,z6]),(1,[z0,z1,z2,z3,z344,z6]),(0,[z0,z1,z20,z71,z3,z5,z6]),(0,[z0,z1,z48,z34,z2,z5,z6]),(0,[z0,z1,z408,z2,z3,z5,z6])],[(0,[z409,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z410]),(0,[z0,z53,z1,z2,z3,z5,z6]),(0,[z70,z0,z1,z2,z3,z411,z6]),(0,[z0,z1,z322,z2,z3,z5,z6]),(0,[z412,z0,z1,z2,z3,z5,z6]),(0,[z413,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z414,z3,z5,z6])],[(0,[z90,z0,z1,z2,z51,z3,z6]),(1,[z85,z1,z2,z3,z5,z75]),(0,[z0,z1,z2,z3,z12,z22,z6])],[(0,[z127,z0,z102,z2,z3,z5,z6]),(0,[z81,z0,z415,z2,z3,z5,z6]),(0,[z0,z416,z1,z2,z3,z5,z6]),(0,[z0,z1,z417,z2,z3,z5,z6]),(0,[z50,z0,z24,z1,z2,z3,z6])],[(0,[z0,z1,z2,z177,z5,z6,z26]),(0,[z418,z0,z1,z2,z3,z5,z6]),(0,[z419,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z420,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z421]),(0,[z0,z1,z2,z3,z5,z6,z422]),(0,[z0,z1,z2,z3,z5,z423,z6]),(1,[z0,z1,z2,z3,z22,z6])]],
   [[(1,[z0,z1,z2,z3,z176,z6]),(0,[z0,z1,z2,z153,z3,z22,z6]),(0,[z0,z1,z2,z424,z3,z5,z6]),(1,[z0,z369,z1,z2,z3,z6]),(0,[z76,z1,z2,z3,z5,z8,z6]),(0,[z0,z1,z2,z141,z3,z22,z6]),(0,[z425,z0,z1,z2,z3,z5,z6]),(0,[z426,z0,z24,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z427,z5,z6])],[(0,[z81,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z428,z3,z5,z6]),(0,[z0,z429,z1,z2,z3,z5,z6]),(0,[z0,z1,z3,z22,z5,z6,z37]),(1,[z0,z430,z2,z3,z5,z6])],[(0,[z0,z431,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z280,z6]),(0,[z0,z432,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z256,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z6]),(0,[z0,z1,z2,z51,z3,z6,z37]),(0,[z0,z1,z2,z3,z5,z6,z433])],[(0,[z0,z1,z2,z3,z434,z5,z6]),(0,[z109,z0,z1,z2,z3,z6,z37]),(0,[z435,z0,z1,z2,z3,z5,z6]),(0,[z0,z96,z1,z141,z3,z5,z6]),(0,[z0,z1,z436,z2,z3,z5,z6]),(1,[z0,z24,z1,z2,z6,z26]),(0,[z0,z1,z2,z3,z79,z6,z80])],[(0,[z0,z1,z102,z2,z3,z6,z37]),(0,[z90,z0,z1,z2,z3,z5,z6]),(0,[z0,z431,z1,z2,z3,z18,z6]),(0,[z437,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z438]),(0,[z439,z0,z1,z2,z3,z22,z6])],[(0,[z0,z1,z2,z251,z3,z5,z6]),(0,[z127,z0,z1,z2,z3,z6,z37]),(0,[z0,z1,z2,z3,z5,z6,z440]),(0,[z441,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z258,z161,z6]),(0,[z0,z1,z3,z5,z6,z442,z26]),(0,[z0,z1,z443,z2,z3,z5,z6])],[(0,[z90,z0,z1,z2,z3,z18,z6]),(0,[z81,z0,z24,z1,z2,z3,z6]),(0,[z0,z444,z1,z2,z3,z6,z37]),(0,[z0,z1,z44,z2,z3,z5,z26])],[(0,[z181,z1,z2,z3,z5,z7,z6]),(1,[z0,z1,z2,z445,z3,z6]),(0,[z0,z166,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z165,z7,z6]),(0,[z121,z0,z96,z2,z3,z5,z6]),(0,[z0,z1,z20,z2,z3,z6,z37]),(0,[z0,z1,z446,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z447])],[(0,[z0,z1,z2,z3,z174,z7,z6]),(0,[z0,z1,z136,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z18,z6,z117]),(0,[z0,z1,z448,z2,z3,z5,z6]),(0,[z0,z24,z1,z449,z2,z3,z6])],[(0,[z0,z1,z450,z2,z3,z5,z6]),(1,[z0,z306,z2,z3,z5,z6]),(0,[z451,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z452]),(0,[z0,z1,z2,z3,z5,z6,z453]),(0,[z0,z1,z454,z2,z3,z5,z6]),(0,[z0,z96,z230,z2,z3,z5,z6]),(0,[z0,z1,z2,z149,z3,z5,z6]),(0,[z0,z1,z2,z3,z22,z6,z37])],[(0,[z91,z109,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z272,z6]),(0,[z90,z0,z1,z2,z3,z229,z6]),(0,[z0,z1,z2,z3,z7,z6,z455]),(0,[z0,z1,z130,z141,z3,z5,z6]),(0,[z0,z230,z2,z3,z5,z97,z6]),(0,[z0,z1,z2,z3,z249,z22,z6]),(0,[z0,z1,z2,z3,z5,z6,z456])],[(0,[z0,z0,z1,z2,z3,z5,z6]),(0,[z85,z1,z2,z36,z3,z5,z6]),(0,[z0,z1,z2,z36,z3,z22,z6]),(0,[z0,z1,z2,z3,z457,z5,z6]),(0,[z0,z24,z1,z2,z141,z3,z6]),(0,[z0,z1,z48,z20,z3,z5,z6]),(0,[z70,z0,z1,z2,z3,z5,z97])],[(0,[z0,z1,z2,z3,z458,z5,z6]),(0,[z0,z1,z2,z3,z5,z459,z6]),(0,[z0,z1,z189,z2,z3,z7,z6]),(0,[z0,z1,z2,z122,z5,z6,z26]),(0,[z0,z1,z34,z2,z122,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z460])],[(0,[z0,z1,z2,z3,z461,z5,z6]),(0,[z0,z1,z462,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z463,z5,z6]),(0,[z0,z0,z1,z2,z3,z18,z6]),(0,[z0,z1,z2,z3,z5,z6,z113]),(0,[z0,z148,z1,z2,z51,z3,z6]),(0,[z0,z1,z2,z3,z5,z11,z6]),(1,[z0,z88,z1,z2,z3,z6]),(0,[z0,z1,z151,z3,z22,z5,z6]),(1,[z0,z1,z2,z321,z3,z6]),(0,[z0,z1,z2,z3,z5,z6,z464]),(0,[z0,z1,z465,z2,z3,z5,z6]),(1,[z0,z1,z2,z466,z5,z6])],[(0,[z0,z148,z1,z195,z3,z5,z6])]],
   [[(0,[z0,z1,z71,z153,z3,z5,z6]),(0,[z0,z1,z131,z2,z51,z3,z6]),(0,[z0,z1,z2,z467,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z468,z6]),(0,[z0,z1,z2,z3,z5,z6,z469]),(0,[z0,z1,z2,z3,z18,z6,z13]),(0,[z0,z1,z71,z141,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z470]),(0,[z0,z1,z2,z3,z30,z5,z6]),(0,[z0,z429,z1,z2,z3,z161,z6]),(0,[z0,z1,z2,z3,z471,z5,z6])],[(0,[z0,z1,z2,z3,z7,z459,z6]),(0,[z0,z1,z34,z2,z3,z7,z6]),(0,[z472,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z114,z6]),(0,[z0,z1,z124,z2,z3,z5,z6])],[(0,[z0,z473,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z7,z11,z6]),(0,[z0,z1,z116,z2,z3,z18,z6]),(0,[z0,z1,z48,z2,z5,z6,z26]),(1,[z0,z1,z2,z3,z140,z6])],[(0,[z0,z1,z2,z3,z12,z7,z6]),(0,[z0,z1,z124,z2,z3,z18,z6]),(0,[z0,z1,z2,z3,z474,z5,z6]),(0,[z76,z0,z1,z2,z3,z6,z37]),(0,[z0,z10,z1,z133,z3,z5,z6]),(0,[z0,z1,z2,z3,z475,z5,z6]),(0,[z56,z0,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z3,z476,z5,z6])],[(0,[z0,z1,z131,z2,z3,z205,z6]),(0,[z0,z1,z131,z3,z5,z6,z117]),(0,[z0,z473,z1,z2,z3,z18,z6]),(0,[z0,z235,z1,z2,z3,z5,z6]),(0,[z0,z477,z1,z2,z3,z5,z6]),(0,[z478,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z479]),(0,[z0,z1,z2,z365,z3,z177,z6]),(1,[z0,z1,z2,z3,z7,z6]),(1,[z0,z262,z2,z3,z5,z6]),(0,[z0,z96,z2,z122,z3,z5,z6]),(0,[z0,z148,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z480,z5,z6]),(0,[z481,z0,z1,z2,z3,z5,z6]),(0,[z482,z0,z1,z2,z3,z5,z6]),(0,[z56,z0,z430,z2,z3,z5,z6]),(0,[z0,z1,z155,z2,z3,z5,z6])],[(1,[z0,z1,z2,z3,z128,z6]),(0,[z0,z1,z2,z153,z3,z7,z6]),(0,[z0,z1,z2,z141,z3,z7,z6]),(0,[z0,z96,z1,z2,z3,z18,z6]),(0,[z483,z0,z1,z2,z3,z5,z6]),(1,[z288,z1,z2,z3,z5,z6]),(0,[z484,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z130,z161,z5,z6]),(0,[z0,z1,z485,z2,z51,z3,z6]),(0,[z0,z1,z2,z3,z5,z6,z486])],[(0,[z0,z1,z131,z2,z3,z5,z6]),(0,[z0,z1,z487,z2,z3,z5,z6]),(0,[z84,z0,z1,z2,z3,z22,z6]),(0,[z0,z148,z1,z2,z3,z18,z6]),(0,[z0,z1,z262,z2,z3,z5,z6]),(0,[z0,z1,z136,z2,z3,z174,z6]),(0,[z70,z488,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z6,z245]),(0,[z489,z0,z1,z2,z3,z5,z6]),(0,[z490,z0,z1,z2,z3,z5,z6]),(0,[z0,z491,z1,z2,z3,z5,z6]),(0,[z0,z23,z148,z2,z3,z5,z6]),(0,[z0,z1,z492,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z22,z493,z6])],[(1,[z137,z1,z2,z3,z7,z6]),(0,[z0,z1,z131,z2,z3,z18,z6]),(0,[z0,z1,z131,z2,z3,z6,z217]),(0,[z81,z0,z494,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z495]),(0,[z0,z1,z2,z3,z5,z6,z496]),(0,[z0,z497,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z51,z12,z5,z6])],[(0,[z137,z1,z2,z36,z3,z5,z6]),(0,[z85,z0,z498,z2,z3,z5,z6]),(0,[z59,z0,z1,z2,z3,z6,z37]),(1,[z0,z24,z1,z2,z3,z6]),(0,[z0,z1,z499,z2,z3,z5,z6])],[(0,[z0,z1,z2,z500,z3,z5,z6]),(0,[z121,z0,z1,z20,z3,z5,z6]),(0,[z121,z0,z1,z2,z3,z6,z37]),(0,[z0,z1,z154,z2,z3,z6,z31]),(0,[z0,z24,z1,z2,z3,z6,z80]),(0,[z0,z1,z2,z501,z3,z5,z6])],[(0,[z91,z1,z2,z36,z3,z5,z6]),(0,[z0,z147,z1,z2,z3,z5,z6]),(0,[z0,z1,z20,z3,z5,z6,z37]),(0,[z0,z502,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z503,z3,z5,z6]),(0,[z0,z473,z1,z2,z36,z3,z6]),(0,[z0,z1,z363,z2,z3,z165,z6]),(0,[z0,z230,z1,z2,z3,z5,z97]),(1,[z185,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z51,z3,z6,z117]),(0,[z0,z1,z2,z3,z5,z250,z6]),(0,[z0,z1,z485,z2,z3,z5,z6])],[(0,[z504,z0,z1,z2,z3,z5,z6]),(0,[z90,z0,z1,z2,z3,z281,z6]),(0,[z76,z0,z1,z2,z3,z19,z6]),(0,[z70,z0,z1,z505,z3,z5,z6]),(0,[z0,z1,z2,z3,z268,z5,z6]),(0,[z0,z1,z34,z2,z3,z99,z5])],[(0,[z137,z0,z1,z2,z51,z3,z6]),(0,[z0,z1,z2,z3,z5,z366,z6]),(0,[z0,z23,z1,z2,z3,z5,z6]),(0,[z0,z1,z506,z2,z3,z5,z6]),(0,[z0,z1,z507,z2,z3,z5,z6]),(0,[z0,z1,z136,z2,z3,z11,z6]),(0,[z0,z1,z508,z48,z2,z3,z6]),(0,[z509,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z151,z2,z3,z6,z37])]],
   [[(0,[z510,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z511,z3,z5,z6]),(0,[z0,z1,z2,z3,z18,z5,z6]),(1,[z0,z1,z2,z3,z30,z6]),(0,[z0,z1,z2,z3,z5,z512,z6])],[(0,[z0,z102,z2,z3,z5,z6,z31]),(0,[z0,z1,z2,z3,z513,z5,z6]),(0,[z0,z23,z1,z2,z3,z18,z6]),(0,[z0,z1,z2,z3,z161,z6,z37]),(0,[z0,z1,z2,z3,z6,z37,z514]),(0,[z0,z1,z44,z2,z51,z3,z6])],[(0,[z0,z1,z2,z36,z3,z7,z6]),(0,[z0,z1,z2,z3,z18,z18,z6]),(0,[z0,z1,z2,z3,z5,z6,z515]),(1,[z260,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z516,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z517]),(1,[z0,z1,z2,z3,z518,z6]),(0,[z0,z1,z519,z2,z3,z5,z6])],[(0,[z49,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z520,z2,z3,z5,z6]),(0,[z0,z1,z255,z2,z3,z7,z6]),(0,[z0,z1,z71,z2,z3,z18,z6]),(0,[z0,z24,z1,z2,z3,z8,z6]),(0,[z0,z1,z2,z3,z22,z6,z521])],[(0,[z0,z156,z1,z2,z3,z5,z6]),(0,[z522,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z51,z3,z6,z13])],[(0,[z0,z1,z2,z3,z5,z523,z6]),(0,[z0,z1,z524,z2,z3,z5,z6]),(0,[z0,z1,z2,z51,z3,z8,z6]),(0,[z0,z1,z525,z2,z3,z5,z6]),(0,[z526,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z508,z2,z3,z6,z37]),(0,[z0,z1,z2,z3,z22,z6,z117]),(0,[z0,z1,z2,z321,z3,z22,z6]),(0,[z0,z1,z2,z3,z5,z6,z527])],[(0,[z137,z0,z1,z2,z3,z5,z6]),(0,[z181,z84,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z528,z3,z5,z6]),(0,[z70,z0,z1,z2,z3,z6,z37]),(0,[z50,z0,z1,z2,z3,z22,z6]),(0,[z0,z1,z136,z2,z3,z79,z6])],[(0,[z181,z0,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z529,z3,z5,z6]),(0,[z0,z325,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z3,z22,z6,z267]),(0,[z0,z1,z2,z3,z5,z530,z6])]],
   [[(0,[z0,z1,z531,z2,z3,z5,z6]),(0,[z0,z1,z130,z2,z3,z22,z6]),(0,[z0,z1,z44,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z532,z5,z6]),(0,[z0,z1,z2,z3,z533,z5,z6]),(0,[z0,z1,z283,z2,z3,z5,z6]),(1,[z1,z2,z3,z18,z7,z6]),(0,[z56,z0,z1,z2,z3,z7,z6]),(0,[z85,z0,z1,z2,z3,z6,z37]),(1,[z0,z1,z2,z3,z273,z6]),(0,[z0,z24,z1,z71,z2,z3,z6]),(0,[z0,z1,z2,z3,z534,z5,z6])],[(0,[z0,z1,z44,z2,z3,z18,z6]),(0,[z0,z1,z2,z3,z18,z6,z26])],[(0,[z1,z102,z2,z3,z5,z7,z6]),(0,[z0,z1,z2,z535,z3,z5,z6]),(0,[z536,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z537,z3,z5,z6]),(0,[z0,z1,z2,z3,z280,z5,z6]),(0,[z1,z2,z36,z3,z177,z5,z6]),(1,[z0,z1,z2,z3,z6,z113]),(0,[z0,z1,z2,z538,z3,z5,z6]),(0,[z0,z1,z2,z3,z79,z6,z37]),(0,[z0,z1,z2,z3,z99,z22,z6]),(0,[z0,z24,z1,z2,z539,z3,z6])],[(0,[z127,z0,z1,z2,z3,z461,z6]),(0,[z0,z24,z1,z131,z2,z3,z6]),(0,[z0,z1,z540,z2,z3,z5,z6]),(0,[z0,z88,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z22,z6,z13]),(0,[z0,z1,z2,z3,z5,z6,z541]),(1,[z0,z1,z2,z3,z66,z6])],[(0,[z137,z0,z216,z2,z3,z5,z6]),(0,[z542,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z48,z153,z3,z5,z6]),(1,[z0,z494,z2,z3,z5,z6]),(0,[z81,z0,z1,z467,z3,z5,z6]),(0,[z84,z0,z1,z2,z3,z7,z6]),(0,[z1,z2,z3,z18,z5,z7,z6]),(0,[z0,z1,z2,z3,z22,z8,z6]),(0,[z0,z1,z48,z141,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z543,z6]),(0,[z0,z1,z2,z3,z544,z5,z6]),(0,[z0,z1,z2,z51,z51,z3,z6])],[(0,[z109,z0,z1,z2,z51,z3,z6]),(0,[z0,z1,z2,z3,z545,z5,z6]),(0,[z546,z0,z1,z2,z3,z5,z6]),(0,[z90,z81,z1,z2,z3,z5,z6]),(0,[z0,z1,z547,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z286,z5,z6]),(0,[z56,z0,z24,z1,z2,z3,z6]),(0,[z0,z1,z2,z548,z3,z5,z6])],[(0,[z0,z1,z549,z2,z3,z5,z6]),(0,[z0,z1,z2,z550,z3,z5,z6]),(0,[z0,z1,z48,z130,z2,z5,z6]),(1,[z0,z1,z2,z3,z152,z6]),(0,[z0,z1,z71,z2,z3,z5,z68]),(0,[z0,z24,z1,z2,z5,z6,z13])]],
   [[(0,[z127,z0,z1,z2,z51,z3,z6]),(0,[z0,z1,z2,z104,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z551]),(0,[z0,z1,z2,z3,z5,z6,z299])],[(0,[z552,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z208,z5,z6]),(0,[z0,z1,z2,z3,z5,z272,z6]),(0,[z90,z0,z1,z2,z36,z5,z6]),(0,[z0,z24,z96,z1,z2,z3,z6]),(0,[z70,z0,z1,z25,z3,z5,z6]),(0,[z56,z185,z1,z2,z3,z5,z6])],[(0,[z84,z0,z24,z1,z2,z3,z6]),(0,[z0,z24,z1,z34,z2,z5,z6])],[(0,[z0,z1,z2,z3,z208,z18,z6]),(0,[z0,z24,z1,z2,z3,z6,z75]),(0,[z0,z1,z20,z2,z51,z3,z6]),(0,[z0,z1,z553,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z68,z6]),(0,[z0,z1,z155,z3,z5,z6,z26])],[(1,[z0,z1,z2,z374,z3,z6]),(1,[z0,z1,z2,z3,z6,z554]),(0,[z0,z1,z2,z51,z3,z5,z6])],[(0,[z84,z1,z102,z2,z3,z5,z6]),(0,[z109,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z229,z5,z6]),(0,[z0,z180,z1,z2,z3,z177,z6]),(0,[z0,z1,z2,z3,z5,z6,z555]),(0,[z0,z1,z2,z51,z3,z6,z75]),(1,[z0,z1,z2,z3,z556,z6])],[(1,[z0,z1,z251,z3,z5,z6]),(0,[z0,z1,z2,z3,z332,z5,z6]),(0,[z0,z24,z1,z2,z3,z97,z6]),(0,[z0,z1,z34,z2,z161,z5,z6]),(0,[z0,z1,z2,z557,z3,z5,z6])],[(0,[z109,z0,z1,z2,z3,z18,z6]),(0,[z0,z1,z20,z3,z5,z6,z117]),(1,[z0,z1,z2,z265,z3,z6]),(0,[z0,z230,z1,z2,z3,z6,z37]),(0,[z0,z88,z1,z48,z2,z3,z6]),(0,[z0,z1,z48,z2,z51,z3,z6])]],
   [[(1,[z0,z1,z222,z3,z5,z6]),(0,[z0,z444,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z51,z3,z97,z6]),(0,[z0,z1,z339,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z558]),(0,[z0,z1,z2,z3,z183,z22,z6])],[(0,[z0,z1,z2,z3,z312,z7,z6]),(0,[z76,z0,z1,z2,z3,z172,z6]),(0,[z0,z1,z2,z3,z258,z5,z6]),(0,[z0,z1,z2,z3,z12,z6,z37]),(0,[z0,z1,z2,z3,z5,z6,z80])],[(0,[z0,z559,z1,z2,z3,z5,z6]),(0,[z0,z1,z20,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z138,z5,z6])],[(0,[z560,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z177,z6,z37]),(0,[z0,z1,z2,z3,z5,z7,z6]),(0,[z561,z0,z1,z2,z3,z5,z6]),(0,[z121,z0,z1,z2,z3,z138,z6]),(0,[z0,z1,z2,z51,z3,z165,z6]),(1,[z0,z1,z149,z3,z5,z6]),(0,[z0,z562,z1,z2,z3,z5,z6]),(1,[z0,z1,z3,z22,z6,z37]),(0,[z0,z1,z2,z3,z5,z6,z514]),(0,[z0,z1,z2,z3,z563,z5,z6])],[(0,[z0,z1,z20,z2,z3,z18,z6]),(1,[z0,z1,z2,z3,z366,z6]),(0,[z260,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z564,z5,z6]),(1,[z0,z429,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z22,z5,z6]),(0,[z0,z1,z2,z3,z565,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z566]),(0,[z0,z216,z2,z122,z3,z5,z6]),(1,[z181,z1,z2,z3,z7,z6]),(0,[z181,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z6,z80]),(0,[z0,z1,z2,z3,z22,z6,z75]),(0,[z0,z1,z567,z2,z3,z5,z6]),(0,[z0,z23,z1,z2,z122,z5,z6]),(0,[z0,z24,z1,z48,z2,z3,z6]),(0,[z186,z0,z1,z2,z3,z5,z6])],[(0,[z127,z0,z216,z2,z3,z5,z6]),(0,[z0,z1,z130,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z22,z18,z6]),(0,[z76,z0,z1,z2,z51,z3,z6]),(0,[z568,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z48,z2,z3,z5,z6]),(0,[z0,z1,z34,z2,z3,z22,z6]),(0,[z56,z0,z1,z2,z3,z5,z117]),(1,[z0,z1,z2,z3,z214,z6])],[(0,[z109,z0,z1,z2,z3,z129,z6]),(1,[z109,z1,z153,z3,z5,z6]),(0,[z0,z1,z2,z374,z36,z3,z6]),(0,[z0,z1,z2,z3,z7,z7,z6]),(0,[z0,z1,z2,z3,z6,z226,z37]),(0,[z0,z1,z44,z2,z5,z6,z26]),(0,[z0,z1,z569,z2,z3,z5,z6])]],
   [[(0,[z81,z0,z1,z2,z177,z5,z6]),(0,[z0,z1,z48,z2,z3,z18,z6]),(0,[z0,z1,z2,z445,z3,z5,z6]),(0,[z0,z1,z2,z3,z570,z5,z6]),(0,[z0,z1,z2,z3,z22,z97,z6]),(0,[z0,z1,z571,z2,z3,z5,z6])],[(1,[z0,z1,z467,z3,z5,z6]),(0,[z0,z1,z338,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z99,z7,z6]),(0,[z0,z53,z1,z2,z3,z18,z6]),(0,[z0,z24,z1,z2,z3,z161,z6]),(0,[z0,z1,z2,z3,z6,z572,z37]),(1,[z0,z1,z2,z573,z5,z6]),(0,[z0,z24,z1,z2,z3,z12,z6])],[(0,[z1,z2,z36,z3,z5,z8,z6]),(0,[z181,z0,z24,z1,z2,z3,z6]),(0,[z0,z1,z2,z445,z3,z18,z6]),(0,[z0,z1,z86,z2,z3,z5,z6]),(0,[z574,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z575]),(0,[z56,z0,z1,z71,z3,z5,z6]),(1,[z1,z2,z3,z5,z6,z111]),(0,[z0,z1,z2,z3,z518,z5,z6])],[(0,[z0,z1,z71,z2,z3,z7,z6]),(0,[z188,z0,z1,z2,z3,z5,z6]),(0,[z85,z0,z1,z2,z104,z5,z6]),(0,[z0,z1,z2,z3,z576,z5,z6]),(0,[z577,z0,z1,z2,z3,z5,z6]),(0,[z578,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z51,z3,z161,z6]),(0,[z0,z24,z1,z2,z3,z6,z37]),(0,[z0,z1,z2,z51,z3,z12,z6]),(0,[z0,z579,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z580,z5,z6])],[(0,[z0,z1,z17,z2,z3,z5,z6]),(0,[z0,z10,z1,z2,z3,z22,z6]),(0,[z0,z1,z581,z2,z3,z5,z6]),(0,[z0,z1,z124,z2,z3,z357,z6]),(1,[z0,z359,z2,z3,z5,z6])],[(0,[z76,z0,z1,z2,z3,z5,z6]),(0,[z0,z2,z141,z122,z3,z5,z6]),(0,[z0,z1,z2,z122,z3,z22,z6]),(0,[z0,z1,z2,z3,z5,z6,z582]),(0,[z59,z0,z1,z2,z51,z3,z6]),(0,[z0,z1,z583,z2,z3,z5,z6])],[(0,[z121,z0,z1,z2,z51,z3,z6]),(0,[z0,z1,z430,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z442])],[(0,[z76,z0,z1,z2,z3,z18,z6]),(0,[z0,z584,z1,z2,z3,z5,z6]),(0,[z0,z1,z585,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z6,z37,z37])]],
   [[(0,[z0,z1,z586,z2,z3,z5,z6]),(0,[z0,z216,z1,z2,z3,z22,z6]),(0,[z0,z377,z1,z2,z3,z5,z6])],[(0,[z0,z1,z131,z141,z3,z5,z6]),(0,[z0,z1,z2,z3,z587,z5,z6]),(0,[z588,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z51,z3,z589,z6])],[(0,[z0,z1,z2,z590,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z455]),(0,[z0,z1,z2,z3,z174,z6,z80]),(0,[z0,z1,z130,z3,z5,z68,z6]),(0,[z0,z1,z591,z2,z3,z5,z6]),(0,[z0,z1,z151,z2,z51,z3,z6]),(0,[z0,z1,z2,z3,z592,z5,z6])],[(0,[z90,z137,z1,z2,z3,z5,z6]),(0,[z593,z0,z1,z2,z3,z5,z6]),(0,[z594,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z212,z6]),(0,[z0,z1,z2,z266,z3,z5,z6]),(0,[z0,z1,z2,z3,z595,z5,z6]),(0,[z0,z352,z24,z1,z2,z3,z6])],[(0,[z121,z0,z2,z141,z3,z5,z6]),(1,[z0,z1,z20,z3,z6,z37]),(0,[z488,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z99,z5,z6,z26]),(0,[z0,z1,z2,z3,z518,z6,z26])],[(0,[z81,z1,z2,z36,z3,z5,z6]),(0,[z0,z369,z1,z2,z3,z7,z6]),(0,[z121,z0,z1,z2,z3,z5,z6]),(0,[z1,z124,z339,z2,z3,z5,z6]),(0,[z0,z1,z2,z2,z3,z6,z37]),(0,[z0,z24,z1,z2,z51,z5,z6]),(0,[z0,z596,z1,z2,z3,z5,z6])],[(0,[z0,z1,z597,z2,z3,z5,z6]),(0,[z70,z0,z230,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z598,z5,z6])],[(0,[z0,z1,z306,z2,z3,z5,z6]),(0,[z121,z0,z1,z2,z3,z18,z6]),(0,[z0,z1,z2,z3,z5,z273,z6]),(0,[z56,z0,z1,z2,z3,z6,z37]),(1,[z0,z1,z2,z3,z599,z6])]],
   [[(0,[z0,z1,z600,z2,z3,z5,z6]),(0,[z0,z601,z1,z2,z3,z5,z6]),(0,[z0,z1,z34,z2,z177,z5,z6]),(0,[z0,z1,z597,z2,z3,z18,z6]),(0,[z0,z1,z2,z3,z6,z75,z37]),(0,[z0,z1,z2,z3,z5,z6,z31]),(0,[z0,z1,z2,z3,z5,z6,z602]),(0,[z0,z1,z508,z2,z51,z3,z6])],[(0,[z0,z10,z2,z3,z5,z11,z6]),(0,[z70,z0,z1,z2,z51,z3,z6]),(0,[z0,z1,z151,z2,z3,z5,z6])],[(1,[z603,z1,z2,z3,z5,z6]),(1,[z0,z2,z3,z5,z6,z100])],[(0,[z90,z0,z1,z2,z3,z22,z6]),(0,[z0,z1,z151,z2,z3,z18,z6]),(0,[z0,z1,z2,z3,z5,z6,z604]),(0,[z426,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z161,z5,z6]),(0,[z0,z24,z1,z34,z2,z3,z6]),(0,[z0,z605,z1,z2,z51,z3,z6]),(0,[z0,z1,z2,z51,z3,z6,z219]),(0,[z0,z2,z3,z5,z6,z100,z26])],[(0,[z606,z0,z1,z2,z3,z5,z6]),(0,[z0,z216,z2,z3,z5,z6,z31]),(0,[z0,z1,z2,z3,z7,z6,z31]),(0,[z85,z0,z1,z2,z51,z3,z6]),(1,[z0,z1,z2,z3,z411,z6]),(0,[z0,z1,z2,z3,z5,z6,z572]),(0,[z0,z1,z2,z3,z5,z6,z143]),(0,[z0,z1,z607,z2,z3,z5,z6])],[(0,[z608,z0,z1,z2,z3,z5,z6]),(0,[z137,z1,z2,z3,z5,z7,z6]),(1,[z0,z415,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z161,z18,z6]),(0,[z56,z0,z1,z2,z573,z5,z6]),(0,[z0,z1,z2,z51,z3,z3,z6]),(0,[z609,z0,z1,z2,z3,z5,z6])],[(0,[z137,z216,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z610,z5,z6]),(0,[z0,z1,z2,z374,z3,z7,z6]),(0,[z0,z1,z2,z611,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z612,z6]),(0,[z0,z1,z20,z151,z3,z5,z6]),(0,[z56,z0,z1,z48,z3,z5,z6]),(0,[z0,z1,z2,z51,z3,z99,z6])],[(0,[z0,z1,z415,z2,z3,z5,z6]),(0,[z0,z1,z613,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z614,z5,z6]),(0,[z0,z1,z2,z3,z411,z5,z6]),(0,[z0,z1,z2,z3,z5,z615,z6]),(0,[z0,z1,z508,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z616,z5,z6])]],
   [[(0,[z0,z1,z2,z617,z3,z5,z6]),(0,[z0,z390,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z618,z5,z6]),(0,[z0,z1,z2,z3,z610,z18,z6]),(0,[z0,z1,z2,z3,z18,z11,z6]),(0,[z70,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z124,z2,z161,z5,z6]),(0,[z0,z24,z1,z116,z2,z3,z6])],[(0,[z0,z96,z20,z2,z3,z5,z6]),(0,[z0,z1,z363,z2,z3,z5,z6]),(0,[z0,z148,z2,z122,z3,z5,z6]),(0,[z0,z53,z10,z2,z3,z5,z6])],[(0,[z91,z0,z1,z153,z3,z5,z6]),(1,[z0,z1,z2,z3,z395,z6]),(0,[z0,z10,z1,z2,z3,z7,z6]),(0,[z70,z0,z1,z2,z3,z18,z6]),(0,[z0,z1,z2,z3,z18,z6,z469]),(0,[z0,z1,z2,z3,z5,z6,z554]),(0,[z298,z0,z1,z2,z3,z6,z37]),(0,[z0,z1,z2,z3,z573,z5,z6]),(0,[z0,z605,z1,z2,z3,z5,z6])],[(0,[z0,z494,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z122,z3,z7,z6]),(0,[z85,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z556,z6])],[(0,[z0,z1,z2,z3,z5,z6,z619]),(0,[z0,z1,z620,z2,z3,z5,z6]),(0,[z14,z1,z2,z3,z5,z6,z26])],[(0,[z0,z1,z2,z621,z3,z5,z6]),(0,[z622,z0,z1,z2,z3,z5,z6]),(1,[z90,z1,z2,z177,z5,z6]),(0,[z85,z0,z1,z2,z3,z18,z6]),(0,[z0,z1,z130,z2,z3,z6,z554]),(0,[z0,z1,z623,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z79,z5,z6])],[(0,[z0,z216,z1,z2,z3,z7,z6]),(0,[z624,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z190,z6]),(0,[z0,z1,z625,z2,z3,z5,z6]),(0,[z0,z24,z1,z2,z3,z6,z117])],[(0,[z626,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z627,z5,z6]),(0,[z0,z1,z628,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z406,z7,z6]),(0,[z0,z1,z2,z3,z79,z18,z6]),(0,[z0,z1,z116,z2,z3,z22,z6]),(0,[z0,z1,z2,z3,z5,z6,z629]),(0,[z0,z1,z2,z199,z3,z5,z6])]],
   [[(1,[z0,z1,z2,z3,z4,z6]),(0,[z70,z235,z1,z2,z3,z5,z6]),(0,[z0,z1,z124,z2,z3,z22,z6]),(0,[z0,z1,z2,z3,z5,z6,z630]),(1,[z0,z24,z1,z34,z2,z6])],[(0,[z0,z53,z1,z2,z3,z7,z6]),(0,[z10,z295,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z631,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z37]),(0,[z0,z1,z2,z3,z632,z5,z6]),(0,[z0,z1,z633,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z634]),(0,[z0,z1,z2,z3,z589,z5,z6]),(0,[z0,z1,z2,z3,z99,z556,z6]),(0,[z0,z635,z1,z2,z3,z5,z6])],[(1,[z0,z1,z2,z3,z461,z6]),(0,[z636,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z637,z5,z6]),(0,[z0,z230,z1,z2,z51,z3,z6]),(0,[z0,z1,z2,z3,z6,z37,z117]),(0,[z50,z0,z1,z2,z3,z6,z37]),(0,[z0,z1,z2,z3,z476,z22,z6])],[(1,[z127,z102,z2,z3,z5,z6]),(0,[z0,z416,z1,z2,z3,z7,z6]),(0,[z0,z96,z1,z2,z3,z22,z6]),(0,[z0,z2,z3,z174,z5,z11,z6]),(0,[z0,z1,z130,z2,z161,z5,z6]),(0,[z56,z0,z1,z2,z3,z599,z6]),(0,[z638,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z214,z5,z6])],[(0,[z639,z0,z1,z2,z3,z5,z6]),(0,[z91,z0,z1,z2,z51,z3,z6]),(0,[z85,z90,z1,z2,z3,z5,z6]),(0,[z0,z148,z1,z2,z3,z22,z6]),(0,[z0,z1,z640,z2,z3,z5,z6]),(0,[z0,z1,z641,z2,z3,z5,z6]),(0,[z0,z1,z642,z2,z3,z5,z6])],[(0,[z643,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z7,z6,z37]),(0,[z644,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z29,z6]),(0,[z0,z1,z2,z3,z98,z6,z37]),(0,[z0,z24,z1,z2,z3,z6,z13])],[(0,[z0,z1,z131,z2,z3,z22,z6]),(0,[z0,z53,z24,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z5,z6,z645]),(1,[z0,z1,z2,z539,z3,z6])],[(0,[z109,z0,z1,z153,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z646,z6]),(0,[z0,z1,z2,z3,z647,z5,z6]),(0,[z70,z0,z1,z2,z3,z160,z6]),(1,[z0,z1,z101,z2,z5,z6])]],
   [[(0,[z137,z0,z1,z2,z3,z207,z6]),(1,[z0,z473,z1,z2,z3,z6]),(0,[z648,z0,z1,z2,z3,z5,z6]),(0,[z0,z230,z2,z141,z3,z5,z6]),(0,[z0,z10,z1,z2,z3,z174,z6]),(0,[z59,z0,z1,z151,z3,z5,z6]),(0,[z0,z497,z1,z2,z3,z22,z6]),(0,[z0,z1,z649,z2,z3,z5,z6])],[(0,[z90,z0,z1,z2,z3,z7,z6]),(0,[z85,z0,z1,z2,z3,z256,z6]),(0,[z0,z1,z2,z650,z3,z5,z6]),(0,[z0,z1,z2,z651,z3,z5,z6]),(0,[z0,z230,z1,z2,z3,z5,z6]),(0,[z70,z0,z1,z2,z266,z5,z6]),(0,[z0,z1,z2,z3,z6,z37,z13]),(1,[z0,z1,z2,z3,z79,z80])],[(0,[z109,z0,z156,z2,z3,z5,z6]),(0,[z81,z0,z1,z2,z3,z6,z37]),(0,[z70,z0,z1,z2,z268,z5,z6]),(0,[z0,z1,z2,z3,z97,z6,z37]),(0,[z0,z1,z2,z3,z652,z5,z6]),(0,[z0,z1,z2,z3,z466,z5,z6])],[(0,[z137,z0,z1,z2,z3,z18,z6]),(0,[z91,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z653,z3,z5,z6]),(0,[z0,z1,z2,z654,z3,z5,z6]),(0,[z0,z230,z1,z2,z3,z18,z6]),(0,[z148,z377,z1,z2,z3,z5,z6])],[(0,[z0,z1,z20,z153,z3,z5,z6]),(0,[z0,z1,z2,z3,z18,z6,z515]),(0,[z0,z1,z2,z3,z5,z655,z6]),(0,[z0,z24,z230,z1,z2,z3,z6])],[(0,[z1,z131,z2,z153,z3,z5,z6]),(0,[z91,z0,z1,z2,z3,z18,z6]),(0,[z0,z1,z656,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z177,z5,z6]),(0,[z0,z657,z1,z2,z3,z5,z6]),(0,[z0,z1,z658,z2,z3,z5,z6]),(0,[z0,z33,z1,z2,z3,z5,z6])],[(0,[z90,z0,z24,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z5,z6,z659]),(0,[z0,z23,z1,z2,z3,z22,z6]),(1,[z0,z1,z154,z2,z3,z6]),(0,[z0,z660,z1,z2,z3,z5,z6]),(0,[z0,z24,z1,z2,z51,z3,z6]),(1,[z14,z1,z2,z3,z5,z6]),(0,[z661,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z116,z2,z466,z5,z6])],[(0,[z91,z137,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z177,z18,z6]),(0,[z0,z1,z2,z3,z662,z5,z6]),(1,[z0,z498,z2,z3,z5,z6]),(0,[z0,z96,z2,z3,z5,z6,z31]),(0,[z0,z24,z148,z1,z2,z3,z6]),(0,[z663,z0,z1,z2,z3,z5,z6]),(1,[z488,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z493,z6])]],
   [[(0,[z0,z10,z1,z2,z3,z11,z6]),(0,[z0,z1,z71,z2,z3,z22,z6])],[(0,[z90,z1,z102,z2,z3,z5,z6]),(0,[z0,z1,z664,z2,z3,z5,z6]),(0,[z0,z0,z1,z2,z3,z7,z6]),(0,[z0,z498,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z165,z6,z37]),(0,[z0,z1,z2,z165,z5,z6,z26]),(0,[z0,z1,z2,z3,z5,z212,z6]),(0,[z0,z1,z665,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z666]),(1,[z0,z202,z2,z3,z5,z6]),(0,[z59,z0,z1,z3,z5,z6,z37]),(1,[z0,z1,z2,z3,z6,z143])],[(0,[z0,z667,z1,z2,z3,z5,z6]),(0,[z0,z1,z102,z2,z51,z3,z6]),(0,[z0,z1,z2,z3,z174,z6,z37]),(0,[z0,z1,z505,z2,z3,z5,z6]),(0,[z0,z1,z136,z2,z3,z6,z37]),(0,[z439,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z539,z3,z5,z6]),(0,[z0,z1,z2,z51,z199,z3,z6])],[(0,[z0,z1,z2,z3,z668,z5,z6]),(0,[z0,z1,z2,z3,z463,z7,z6]),(0,[z0,z1,z2,z3,z5,z669,z6]),(1,[z295,z1,z2,z3,z5,z6]),(0,[z603,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z449,z2,z3,z5,z6]),(0,[z0,z1,z670,z2,z3,z5,z6]),(0,[z0,z1,z116,z2,z3,z6,z80])],[(0,[z137,z84,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z671]),(0,[z0,z1,z2,z672,z3,z5,z6]),(0,[z0,z1,z673,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z674,z5,z6]),(0,[z56,z0,z166,z2,z3,z5,z6])],[(0,[z0,z1,z116,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z668,z18,z6]),(0,[z85,z0,z1,z107,z3,z5,z6]),(0,[z675,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z599,z6]),(0,[z0,z24,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z676,z3,z5,z6])],[(0,[z137,z0,z1,z2,z3,z176,z6]),(0,[z91,z1,z131,z2,z3,z5,z6]),(0,[z0,z677,z1,z2,z3,z5,z6]),(0,[z0,z1,z124,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z5,z678,z6]),(0,[z0,z679,z1,z2,z3,z5,z6]),(0,[z0,z148,z1,z2,z122,z5,z6]),(1,[z0,z1,z505,z3,z5,z6]),(0,[z0,z1,z680,z2,z3,z5,z6])],[(0,[z0,z681,z1,z2,z3,z5,z6]),(0,[z0,z24,z1,z2,z3,z18,z6]),(0,[z0,z10,z1,z2,z3,z79,z6]),(0,[z0,z53,z1,z2,z3,z11,z6]),(1,[z0,z1,z3,z5,z6,z442])]],
   [[(0,[z0,z1,z682,z2,z3,z5,z6]),(0,[z603,z1,z124,z2,z3,z5,z6]),(0,[z0,z1,z683,z2,z3,z5,z6])],[(0,[z0,z1,z102,z2,z3,z5,z6]),(0,[z0,z96,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z51,z3,z18,z6]),(0,[z684,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z685,z2,z3,z5,z6]),(0,[z0,z24,z1,z20,z2,z3,z6]),(0,[z0,z1,z2,z3,z5,z6,z686]),(0,[z0,z1,z687,z2,z51,z3,z6])],[(0,[z127,z0,z1,z2,z3,z5,z6]),(0,[z0,z688,z1,z2,z3,z5,z6]),(0,[z0,z148,z1,z2,z3,z7,z6]),(0,[z0,z1,z34,z2,z3,z6,z37]),(0,[z0,z1,z2,z3,z5,z6,z521]),(0,[z56,z0,z1,z2,z51,z3,z6]),(0,[z0,z1,z2,z3,z5,z6,z689])],[(0,[z0,z1,z102,z2,z3,z18,z6]),(0,[z0,z690,z1,z2,z3,z5,z6]),(0,[z0,z88,z1,z2,z3,z22,z6])],[(0,[z127,z0,z1,z2,z3,z18,z6]),(0,[z0,z1,z131,z2,z3,z7,z6]),(0,[z0,z24,z1,z2,z3,z165,z6]),(0,[z0,z1,z2,z3,z5,z6,z691]),(0,[z0,z1,z2,z3,z5,z6,z117]),(0,[z0,z473,z24,z1,z2,z3,z6])],[(0,[z692,z0,z1,z2,z3,z5,z6]),(0,[z0,z24,z216,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z5,z6,z693]),(0,[z0,z1,z2,z3,z18,z68,z6]),(0,[z546,z0,z1,z2,z3,z22,z6]),(0,[z368,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z694,z6])],[(0,[z127,z137,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z93,z5,z6]),(0,[z0,z53,z1,z2,z3,z79,z6]),(1,[z0,z1,z2,z3,z6,z37]),(0,[z0,z1,z2,z51,z3,z246,z6])],[(0,[z0,z1,z2,z2,z3,z5,z6]),(0,[z0,z1,z2,z153,z3,z6,z37]),(0,[z121,z0,z1,z141,z3,z5,z6]),(0,[z0,z1,z2,z141,z3,z6,z37]),(0,[z0,z1,z695,z2,z3,z5,z6]),(0,[z0,z24,z1,z2,z3,z6,z26])]],
   [[(0,[z0,z24,z1,z2,z36,z3,z6]),(0,[z0,z1,z2,z3,z7,z6,z117]),(0,[z0,z1,z2,z3,z5,z395,z6]),(0,[z0,z1,z2,z3,z11,z6,z80]),(0,[z0,z1,z2,z3,z5,z303,z6]),(0,[z0,z1,z2,z3,z208,z22,z6]),(1,[z0,z1,z2,z3,z43,z6]),(0,[z0,z1,z687,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z696]),(0,[z697,z0,z1,z2,z3,z5,z6]),(0,[z698,z0,z1,z2,z3,z5,z6]),(0,[z56,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z51,z3,z6,z26])],[(1,[z1,z102,z2,z3,z7,z6]),(0,[z0,z102,z2,z141,z3,z5,z6]),(0,[z0,z1,z2,z51,z36,z3,z6]),(0,[z0,z1,z2,z3,z699,z5,z6]),(0,[z0,z1,z700,z2,z3,z5,z6]),(0,[z0,z1,z553,z2,z3,z22,z6])],[(0,[z0,z1,z2,z3,z18,z6,z80]),(0,[z0,z1,z151,z141,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z13])],[(0,[z1,z102,z2,z3,z5,z6,z75]),(0,[z0,z23,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z5,z8,z6]),(0,[z0,z24,z1,z151,z2,z3,z6]),(0,[z0,z701,z1,z2,z3,z5,z6]),(0,[z0,z702,z1,z2,z3,z5,z6]),(0,[z0,z1,z116,z101,z2,z5,z6])],[(0,[z0,z1,z2,z3,z18,z7,z6]),(0,[z85,z0,z1,z2,z332,z5,z6]),(1,[z0,z1,z508,z2,z3,z6])],[(0,[z81,z0,z1,z2,z36,z5,z6]),(0,[z0,z1,z2,z703,z3,z5,z6]),(0,[z0,z1,z34,z2,z165,z5,z6]),(0,[z0,z1,z3,z5,z68,z6,z117]),(0,[z0,z1,z2,z3,z152,z5,z6]),(0,[z0,z1,z704,z2,z3,z5,z6])],[(0,[z0,z705,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z7,z6,z13]),(0,[z0,z1,z2,z3,z706,z5,z6]),(0,[z0,z24,z1,z130,z2,z3,z6]),(1,[z59,z0,z1,z3,z6,z37]),(0,[z0,z238,z1,z2,z3,z6,z37]),(0,[z0,z1,z136,z116,z2,z3,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z6,z707]),(0,[z0,z416,z2,z3,z459,z6])],[(0,[z0,z1,z2,z3,z461,z6]),(0,[z91,z1,z2,z3,z140,z6]),(0,[z85,z1,z2,z3,z7,z75]),(0,[z0,z708,z1,z2,z3,z6]),(0,[z85,z262,z2,z3,z5,z75]),(0,[z121,z0,z141,z3,z273,z6]),(0,[z0,z1,z3,z183,z6,z37]),(0,[z0,z359,z2,z122,z5,z6])],[(0,[z0,z1,z2,z3,z709,z6]),(0,[z0,z1,z2,z3,z710,z6]),(0,[z0,z10,z133,z3,z11,z6])],[(0,[z90,z1,z2,z177,z229,z6]),(0,[z0,z1,z2,z3,z711,z6]),(0,[z0,z712,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z713,z6]),(0,[z288,z1,z2,z3,z714,z6]),(0,[z0,z1,z2,z3,z715,z6]),(0,[z0,z1,z716,z2,z3,z6]),(0,[z64,z1,z48,z3,z5,z6])],[(0,[z0,z1,z2,z3,z717,z6]),(0,[z0,z430,z2,z3,z7,z6]),(0,[z718,z1,z2,z3,z5,z6]),(0,[z70,z0,z2,z51,z3,z31]),(0,[z0,z1,z719,z3,z5,z6]),(0,[z0,z1,z2,z539,z3,z6]),(0,[z0,z1,z2,z3,z720,z6])],[(0,[z85,z24,z1,z2,z3,z75]),(0,[z0,z1,z335,z3,z6,z37]),(0,[z0,z1,z2,z3,z6,z721]),(0,[z1,z3,z5,z6,z442,z111]),(0,[z0,z1,z2,z3,z722,z6]),(0,[z0,z1,z723,z3,z5,z6])],[(0,[z0,z1,z724,z3,z5,z6]),(0,[z0,z1,z2,z3,z93,z6]),(0,[z298,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z725,z6]),(0,[z0,z1,z3,z204,z6,z37])],[(0,[z0,z726,z1,z2,z3,z6]),(0,[z188,z0,z1,z3,z6,z245]),(0,[z0,z1,z727,z2,z3,z6]),(0,[z728,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z79,z80])],[(0,[z0,z1,z2,z3,z729,z6]),(0,[z0,z1,z2,z3,z730,z6]),(0,[z522,z0,z1,z3,z6,z37]),(0,[z0,z1,z2,z3,z731,z6]),(0,[z0,z732,z2,z3,z5,z6])],[(0,[z561,z102,z2,z3,z5,z6]),(0,[z0,z473,z1,z34,z2,z6]),(0,[z0,z24,z1,z2,z518,z6]),(0,[z0,z1,z2,z3,z6,z733])],[(0,[z0,z1,z487,z2,z5,z26]),(0,[z0,z1,z734,z2,z3,z6]),(0,[z735,z1,z2,z3,z5,z6]),(0,[z295,z1,z2,z51,z3,z6]),(0,[z64,z1,z130,z3,z5,z6]),(0,[z0,z1,z3,z736,z6,z442])],[(0,[z0,z1,z2,z3,z5,z6]),(0,[z0,z737,z1,z2,z3,z6]),(0,[z412,z1,z2,z3,z7,z6]),(0,[z0,z1,z3,z5,z6,z738]),(0,[z0,z1,z739,z3,z5,z6]),(0,[z0,z24,z1,z133,z3,z6]),(0,[z0,z24,z1,z2,z268,z6]),(0,[z603,z284,z2,z3,z5,z6]),(0,[z0,z166,z2,z57,z5,z6])],[(0,[z296,z0,z141,z3,z5,z6]),(0,[z0,z10,z322,z2,z3,z6]),(0,[z235,z1,z2,z51,z3,z6]),(0,[z185,z430,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z18,z6]),(0,[z0,z498,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z740,z6]),(0,[z0,z306,z2,z3,z7,z6]),(0,[z0,z238,z141,z3,z6,z37]),(0,[z0,z1,z2,z3,z5,z741]),(0,[z0,z1,z505,z51,z3,z6]),(0,[z59,z0,z1,z539,z3,z6])],[(0,[z0,z1,z2,z3,z463,z223]),(0,[z0,z1,z2,z3,z742,z6]),(0,[z0,z1,z44,z155,z5,z26])]],
   [[(0,[z0,z1,z2,z3,z6,z743]),(0,[z0,z1,z2,z3,z6,z744]),(0,[z0,z498,z2,z3,z18,z6]),(0,[z0,z1,z2,z3,z745,z6]),(0,[z0,z202,z2,z3,z5,z6]),(0,[z0,z746,z2,z3,z5,z6])],[(0,[z0,z1,z2,z747,z3,z6]),(0,[z0,z24,z1,z2,z3,z748])],[(0,[z510,z102,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z749,z6]),(0,[z1,z2,z3,z177,z140,z6]),(0,[z0,z1,z2,z3,z750,z6]),(0,[z0,z202,z2,z3,z18,z6]),(0,[z0,z1,z124,z3,z6,z113]),(0,[z0,z1,z2,z751,z3,z6]),(0,[z0,z1,z101,z2,z22,z6])],[(0,[z0,z1,z2,z3,z752,z6]),(0,[z1,z2,z153,z3,z140,z6]),(0,[z0,z1,z2,z3,z229,z6]),(0,[z0,z1,z2,z3,z753,z6]),(0,[z0,z1,z520,z3,z6,z37]),(0,[z0,z1,z2,z754,z3,z6]),(0,[z755,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z756,z3,z6])],[(0,[z0,z1,z2,z3,z757,z6]),(0,[z0,z1,z2,z3,z758,z6]),(0,[z0,z23,z149,z3,z5,z6]),(0,[z0,z759,z2,z3,z5,z6])],[(0,[z127,z24,z102,z2,z3,z6]),(0,[z70,z0,z505,z3,z5,z31]),(0,[z0,z1,z2,z760,z3,z6])],[(1,[z306,z153,z3,z5,z6]),(0,[z0,z1,z2,z3,z761,z6]),(0,[z0,z1,z86,z3,z366,z6]),(0,[z0,z1,z2,z3,z762,z6]),(0,[z0,z763,z1,z2,z3,z6]),(0,[z377,z1,z2,z3,z6,z37]),(0,[z24,z1,z339,z2,z3,z6]),(0,[z0,z764,z2,z3,z5,z6]),(0,[z0,z3,z5,z6,z442,z100])],[(0,[z0,z1,z2,z3,z765,z6]),(0,[z0,z1,z2,z3,z766,z6])],[(0,[z0,z1,z2,z3,z767,z6]),(0,[z0,z1,z2,z3,z768,z6])],[(0,[z102,z2,z251,z3,z5,z6]),(0,[z0,z769,z2,z3,z5,z6]),(0,[z0,z1,z2,z770,z3,z6]),(0,[z0,z24,z1,z771,z3,z6])],[(0,[z0,z1,z2,z3,z772,z6]),(0,[z0,z1,z2,z3,z773,z6]),(0,[z0,z494,z467,z3,z5,z6]),(0,[z0,z1,z2,z3,z256,z6]),(0,[z0,z774,z1,z2,z3,z6]),(0,[z147,z96,z2,z3,z5,z6]),(0,[z0,z1,z3,z5,z6,z775]),(0,[z488,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z776,z3,z6]),(0,[z0,z1,z2,z3,z258,z6]),(0,[z49,z125,z1,z2,z3,z6])],[(0,[z0,z777,z1,z2,z3,z6]),(0,[z0,z494,z2,z3,z22,z6]),(0,[z0,z1,z2,z3,z778,z6]),(0,[z70,z0,z2,z3,z160,z31]),(0,[z339,z202,z2,z3,z5,z6])],[(0,[z0,z24,z1,z222,z3,z6]),(0,[z0,z1,z20,z3,z6,z245]),(0,[z0,z498,z2,z3,z256,z6]),(0,[z0,z1,z2,z779,z3,z6]),(0,[z0,z1,z2,z6,z780,z13])],[(0,[z0,z24,z1,z83,z3,z6]),(0,[z235,z1,z505,z3,z5,z6]),(0,[z0,z1,z640,z2,z5,z26]),(0,[z0,z1,z2,z3,z476,z267]),(0,[z353,z1,z2,z374,z3,z6])],[(0,[z0,z24,z1,z2,z6,z619]),(0,[z0,z781,z2,z3,z5,z6]),(0,[z782,z1,z2,z3,z22,z6])],[(0,[z0,z1,z2,z3,z6,z783]),(0,[z0,z1,z2,z784,z5,z6]),(0,[z0,z1,z20,z3,z6,z217]),(0,[z0,z1,z107,z51,z3,z6])]],
   [[(0,[z0,z1,z586,z3,z6,z37]),(0,[z0,z1,z467,z3,z785,z6]),(0,[z0,z1,z2,z3,z786,z6])],[(0,[z0,z1,z2,z787,z3,z6]),(0,[z0,z1,z3,z68,z6,z113]),(0,[z0,z24,z1,z2,z573,z6]),(0,[z0,z24,z1,z2,z6,z629]),(0,[z0,z1,z2,z3,z788,z6])],[(0,[z0,z1,z2,z3,z789,z6]),(0,[z64,z166,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z790,z6]),(0,[z1,z2,z3,z7,z6,z226]),(0,[z0,z1,z791,z3,z5,z6]),(0,[z0,z1,z133,z51,z3,z6]),(0,[z235,z1,z2,z3,z160,z6])],[(0,[z0,z1,z2,z792,z3,z6]),(0,[z0,z1,z505,z3,z160,z6]),(0,[z0,z1,z508,z2,z3,z6]),(0,[z603,z1,z2,z3,z357,z6]),(0,[z0,z1,z2,z3,z793,z6])],[(0,[z0,z1,z2,z794,z3,z6]),(0,[z0,z1,z2,z795,z3,z6]),(0,[z0,z1,z2,z3,z6,z796])],[(0,[z0,z1,z222,z3,z22,z6]),(0,[z0,z1,z2,z3,z797,z6]),(0,[z377,z1,z2,z3,z212,z6]),(0,[z0,z238,z2,z3,z6,z67])],[(0,[z0,z798,z1,z2,z3,z6]),(0,[z0,z1,z799,z2,z3,z6]),(0,[z800,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z6,z801]),(0,[z0,z1,z2,z3,z802,z6])],[(0,[z0,z1,z803,z2,z3,z6]),(0,[z0,z473,z1,z804,z3,z6]),(0,[z0,z369,z1,z2,z51,z6]),(0,[z0,z1,z101,z2,z7,z6]),(0,[z0,z1,z805,z2,z3,z6]),(0,[z0,z1,z25,z3,z5,z6]),(0,[z0,z1,z806,z2,z3,z6]),(0,[z0,z1,z25,z3,z807,z6]),(0,[z0,z1,z2,z3,z286,z6]),(0,[z64,z1,z2,z51,z3,z6]),(0,[z0,z1,z2,z3,z808,z6])],[(0,[z102,z2,z3,z5,z6,z479]),(1,[z147,z141,z3,z5,z6]),(0,[z0,z1,z809,z2,z3,z6]),(0,[z0,z1,z48,z55,z2,z6])],[(0,[z102,z2,z141,z3,z7,z6]),(0,[z0,z1,z25,z3,z18,z6]),(0,[z810,z1,z2,z3,z5,z6]),(0,[z252,z1,z2,z3,z6,z37]),(0,[z0,z1,z2,z3,z811,z6]),(0,[z0,z1,z55,z2,z6,z221]),(0,[z0,z1,z812,z2,z3,z6])],[(0,[z0,z369,z1,z2,z6,z13]),(0,[z1,z2,z3,z18,z6,z111]),(0,[z0,z1,z2,z3,z6,z813]),(0,[z0,z1,z2,z518,z466,z6])],[(0,[z137,z1,z2,z3,z19,z6]),(0,[z0,z1,z2,z814,z3,z6]),(0,[z121,z0,z24,z141,z3,z6]),(0,[z0,z1,z2,z3,z815,z6]),(0,[z1,z816,z2,z3,z5,z6])],[(0,[z109,z1,z153,z3,z22,z6]),(0,[z0,z1,z2,z817,z3,z6]),(0,[z1,z2,z3,z5,z6,z818]),(0,[z147,z1,z2,z3,z6,z37]),(0,[z0,z1,z819,z3,z5,z6]),(0,[z0,z1,z2,z3,z54,z6]),(0,[z0,z88,z1,z539,z3,z6])],[(0,[z56,z0,z1,z3,z6,z113])],[(0,[z0,z1,z2,z3,z820,z6]),(0,[z14,z1,z2,z3,z7,z6]),(0,[z0,z2,z3,z5,z6,z821])]],
   [[(0,[z0,z1,z822,z3,z5,z6]),(0,[z488,z1,z2,z3,z7,z6]),(0,[z147,z1,z2,z3,z823,z6]),(0,[z0,z1,z2,z3,z824,z6]),(0,[z0,z1,z2,z825,z5,z6])],[(0,[z192,z102,z2,z3,z5,z6]),(0,[z91,z1,z131,z3,z6,z37]),(0,[z0,z1,z2,z826,z3,z6]),(0,[z0,z149,z122,z3,z5,z6]),(0,[z0,z1,z2,z3,z827,z6]),(0,[z0,z1,z2,z828,z268,z6]),(0,[z0,z430,z2,z573,z5,z6]),(0,[z0,z1,z2,z3,z829,z6]),(0,[z1,z830,z2,z3,z5,z6])],[(0,[z0,z359,z2,z3,z22,z6]),(0,[z0,z1,z61,z2,z3,z6]),(0,[z0,z831,z1,z2,z3,z6])],[(0,[z90,z1,z2,z168,z5,z6]),(0,[z0,z1,z2,z832,z7,z6]),(0,[z0,z1,z3,z114,z6,z37])],[(0,[z0,z1,z833,z2,z5,z6]),(0,[z0,z834,z2,z3,z5,z6]),(0,[z0,z1,z835,z2,z3,z6]),(0,[z0,z1,z2,z3,z836,z6]),(0,[z14,z24,z1,z2,z3,z6]),(0,[z1,z155,z3,z5,z6,z111])],[(0,[z488,z24,z1,z2,z3,z6])],[(0,[z56,z0,z166,z3,z5,z117]),(0,[z0,z24,z1,z3,z6,z442])],[(0,[z0,z1,z2,z3,z5,z818]),(0,[z0,z1,z2,z837,z3,z6]),(0,[z252,z1,z133,z3,z5,z6])],[(0,[z0,z1,z838,z2,z3,z6]),(0,[z0,z498,z2,z332,z5,z6]),(0,[z839,z1,z2,z3,z5,z6]),(0,[z0,z1,z840,z2,z5,z6]),(0,[z0,z284,z2,z3,z6,z37]),(0,[z186,z0,z1,z2,z3,z299])],[(0,[z0,z1,z841,z3,z5,z6]),(0,[z0,z1,z3,z208,z6,z113]),(0,[z0,z1,z2,z3,z842,z6]),(0,[z0,z1,z25,z266,z5,z6])],[(0,[z0,z1,z25,z268,z5,z6])],[(0,[z0,z1,z843,z2,z3,z6]),(0,[z0,z2,z3,z18,z6,z100]),(0,[z0,z1,z107,z3,z844,z6]),(0,[z0,z1,z2,z3,z6,z845]),(0,[z1,z2,z3,z5,z6,z846]),(0,[z847,z1,z2,z3,z5,z6]),(0,[z848,z1,z2,z3,z5,z6]),(0,[z849,z1,z2,z3,z5,z6]),(0,[z0,z24,z1,z6,z442,z26]),(0,[z0,z1,z850,z3,z5,z6])],[(0,[z0,z1,z222,z3,z851,z6]),(0,[z137,z102,z2,z3,z7,z6]),(0,[z91,z306,z2,z3,z5,z6]),(0,[z0,z1,z55,z20,z3,z6]),(0,[z0,z1,z852,z2,z3,z6]),(0,[z64,z1,z2,z57,z5,z6])],[(0,[z1,z2,z3,z5,z853,z6]),(0,[z0,z1,z854,z3,z5,z6]),(0,[z0,z1,z855,z3,z5,z6]),(0,[z856,z0,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z857,z6]),(0,[z681,z102,z2,z3,z5,z6]),(0,[z1,z339,z2,z3,z750,z6]),(0,[z0,z1,z155,z3,z6,z733])],[(0,[z0,z1,z854,z3,z18,z6]),(0,[z0,z262,z2,z3,z6,z37]),(0,[z0,z858,z1,z2,z3,z6]),(0,[z0,z1,z2,z859,z5,z6]),(0,[z1,z2,z51,z3,z6,z111])]],
   [[(0,[z0,z1,z2,z3,z860,z6]),(0,[z0,z1,z861,z3,z5,z6]),(0,[z0,z24,z262,z2,z3,z6]),(0,[z862,z1,z2,z3,z5,z6]),(0,[z0,z1,z83,z3,z22,z6]),(0,[z0,z1,z2,z863,z3,z6]),(0,[z0,z1,z155,z3,z5,z6]),(0,[z603,z1,z2,z3,z22,z6])],[(0,[z0,z156,z2,z3,z5,z6]),(0,[z353,z1,z2,z3,z7,z6]),(0,[z0,z1,z864,z2,z6,z37])],[(0,[z0,z1,z2,z865,z3,z6]),(0,[z0,z1,z155,z3,z18,z6]),(0,[z866,z1,z2,z3,z5,z6])],[(0,[z0,z156,z2,z3,z18,z6]),(0,[z109,z1,z153,z3,z7,z6]),(0,[z0,z1,z2,z3,z172,z6]),(0,[z0,z1,z867,z3,z5,z6]),(0,[z0,z1,z868,z2,z3,z6]),(0,[z0,z24,z1,z2,z244,z6])],[(0,[z0,z1,z869,z3,z5,z6]),(0,[z0,z1,z3,z22,z6,z113]),(0,[z0,z1,z2,z770,z266,z6]),(0,[z870,z1,z2,z3,z22,z6]),(0,[z0,z155,z3,z5,z6,z100])],[(0,[z127,z102,z251,z3,z5,z6]),(0,[z0,z1,z2,z871,z3,z6]),(0,[z0,z180,z1,z2,z3,z6]),(0,[z0,z230,z141,z3,z6,z37]),(0,[z0,z2,z3,z872,z5,z6]),(0,[z0,z1,z2,z3,z873,z6]),(0,[z0,z24,z1,z2,z6,z13])],[(0,[z0,z874,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z875,z6]),(0,[z482,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z6,z876]),(0,[z0,z1,z2,z3,z877,z6]),(0,[z0,z1,z878,z3,z5,z6])],[(0,[z0,z1,z2,z3,z6,z879]),(0,[z0,z1,z880,z3,z5,z6]),(0,[z0,z1,z2,z3,z881,z6]),(0,[z0,z1,z2,z3,z882,z6]),(0,[z0,z1,z2,z3,z6,z883])],[(0,[z0,z1,z2,z3,z6,z884]),(0,[z0,z359,z2,z3,z7,z6]),(0,[z0,z1,z885,z2,z6,z37])],[(0,[z0,z369,z1,z2,z36,z6]),(0,[z0,z886,z1,z2,z3,z6]),(0,[z0,z1,z195,z3,z5,z6]),(0,[z0,z1,z2,z3,z887,z6]),(0,[z0,z1,z2,z3,z888,z6]),(0,[z1,z2,z3,z889,z6,z111])],[(0,[z0,z1,z2,z199,z3,z6]),(0,[z0,z890,z2,z3,z5,z6]),(0,[z0,z1,z891,z2,z3,z6]),(0,[z0,z1,z2,z892,z5,z6]),(0,[z0,z1,z2,z3,z893,z6])],[(0,[z23,z102,z2,z3,z7,z6]),(0,[z293,z1,z153,z3,z5,z6]),(0,[z0,z1,z131,z3,z6,z113]),(0,[z0,z1,z195,z3,z18,z6])],[(0,[z0,z1,z283,z3,z6,z37]),(0,[z0,z1,z894,z2,z3,z6]),(0,[z260,z1,z2,z3,z6,z37]),(0,[z0,z1,z719,z161,z5,z6])],[(0,[z0,z1,z2,z895,z5,z6]),(0,[z0,z24,z667,z1,z2,z6]),(0,[z147,z1,z2,z3,z138,z6]),(0,[z235,z230,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z79,z267]),(0,[z0,z1,z896,z3,z5,z6]),(0,[z1,z2,z3,z518,z6,z111])],[(0,[z0,z1,z2,z3,z897,z6]),(0,[z0,z1,z2,z3,z6,z898]),(0,[z0,z1,z2,z3,z6,z245]),(0,[z0,z1,z86,z3,z899,z6]),(0,[z0,z166,z2,z3,z22,z6]),(0,[z0,z1,z900,z2,z3,z6])],[(0,[z0,z1,z901,z3,z5,z6]),(0,[z0,z1,z2,z3,z902,z6]),(0,[z292,z1,z2,z3,z18,z6]),(0,[z0,z1,z508,z20,z3,z6]),(0,[z0,z1,z2,z3,z807,z6]),(0,[z0,z1,z2,z3,z903,z6]),(0,[z0,z1,z2,z904,z5,z6]),(0,[z0,z2,z51,z3,z6,z100])]],
   [[(0,[z643,z1,z153,z3,z5,z6]),(0,[z0,z1,z42,z3,z22,z6]),(0,[z288,z1,z2,z3,z212,z6])],[(0,[z127,z102,z2,z3,z22,z6]),(0,[z0,z1,z2,z3,z6,z217]),(0,[z188,z0,z1,z3,z6,z37]),(0,[z0,z1,z107,z104,z5,z6]),(0,[z0,z1,z2,z3,z6,z905])],[(0,[z0,z906,z2,z3,z5,z6]),(0,[z0,z24,z1,z2,z57,z6])],[(0,[z0,z1,z2,z3,z5,z907]),(0,[z1,z2,z3,z5,z6,z908])],[(0,[z0,z1,z909,z3,z5,z6]),(0,[z0,z1,z2,z910,z3,z6]),(0,[z0,z1,z2,z3,z911,z6]),(0,[z0,z10,z2,z3,z616,z6]),(0,[z0,z1,z55,z2,z3,z6]),(0,[z2,z3,z5,z6,z100,z111])],[(0,[z0,z1,z20,z3,z6,z113]),(0,[z23,z377,z2,z3,z5,z6]),(0,[z0,z1,z912,z3,z5,z6]),(0,[z252,z1,z2,z51,z3,z6]),(0,[z0,z1,z2,z913,z3,z6]),(0,[z0,z359,z2,z3,z518,z6])],[(0,[z0,z914,z1,z2,z3,z6]),(0,[z603,z1,z2,z3,z7,z6]),(0,[z0,z1,z83,z3,z7,z6]),(0,[z121,z0,z141,z3,z6,z37]),(0,[z915,z1,z2,z3,z5,z6]),(0,[z0,z1,z34,z2,z539,z6])],[(0,[z0,z1,z2,z3,z916,z6]),(0,[z0,z1,z2,z3,z344,z6]),(0,[z0,z10,z2,z3,z872,z6]),(0,[z917,z1,z2,z3,z22,z6]),(0,[z0,z1,z44,z2,z22,z26])],[(0,[z0,z1,z86,z3,z6,z37]),(0,[z147,z1,z2,z51,z3,z6]),(0,[z235,z2,z122,z3,z5,z6])],[(0,[z369,z1,z102,z2,z3,z6]),(0,[z1,z339,z2,z3,z54,z6]),(0,[z0,z918,z1,z2,z57,z6])],[(0,[z0,z1,z2,z3,z5,z919]),(0,[z0,z1,z920,z3,z5,z6]),(0,[z0,z1,z921,z3,z5,z6]),(0,[z0,z1,z2,z3,z6,z922]),(0,[z0,z1,z2,z3,z923,z6]),(0,[z0,z23,z2,z342,z5,z6]),(0,[z0,z924,z2,z3,z5,z6]),(0,[z0,z1,z3,z6,z634,z37])],[(0,[z0,z1,z3,z161,z6,z113]),(0,[z439,z1,z2,z3,z18,z6]),(0,[z85,z498,z2,z3,z5,z75]),(0,[z0,z1,z2,z3,z925,z6]),(0,[z0,z1,z926,z2,z3,z6]),(0,[z0,z1,z2,z3,z714,z6]),(0,[z603,z24,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z176,z6]),(0,[z927,z1,z2,z3,z5,z6]),(0,[z14,z1,z2,z3,z22,z6])],[(0,[z0,z928,z2,z3,z5,z6]),(0,[z0,z929,z1,z2,z3,z6]),(0,[z930,z1,z2,z3,z5,z6]),(0,[z0,z88,z1,z2,z321,z6]),(0,[z0,z2,z3,z518,z6,z100])],[(0,[z0,z1,z2,z3,z6,z931]),(0,[z1,z932,z153,z3,z5,z6]),(0,[z0,z1,z2,z3,z933,z6]),(0,[z0,z934,z1,z2,z3,z6]),(0,[z147,z2,z141,z3,z5,z6]),(0,[z935,z1,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z6,z936]),(0,[z0,z1,z2,z3,z937,z6]),(0,[z0,z938,z2,z3,z5,z6])],[(0,[z109,z1,z932,z3,z5,z6]),(0,[z0,z1,z3,z395,z6,z245]),(0,[z0,z1,z939,z2,z3,z6]),(0,[z0,z1,z804,z3,z5,z6]),(0,[z0,z369,z1,z124,z2,z6]),(0,[z0,z1,z2,z3,z940,z6])]],
   [[(0,[z0,z1,z251,z3,z6,z37]),(0,[z137,z369,z1,z2,z3,z6]),(0,[z84,z1,z2,z3,z6,z226]),(0,[z0,z1,z3,z18,z6,z442]),(0,[z0,z24,z1,z107,z3,z6]),(0,[z0,z1,z2,z3,z6,z941]),(0,[z0,z1,z2,z266,z5,z6]),(0,[z0,z1,z2,z3,z942,z6])],[(0,[z0,z943,z1,z2,z5,z6]),(0,[z0,z1,z804,z3,z18,z6]),(0,[z0,z24,z498,z2,z3,z6]),(0,[z0,z1,z2,z268,z5,z6]),(0,[z295,z1,z2,z3,z22,z6]),(0,[z235,z1,z2,z3,z944,z6]),(0,[z0,z430,z71,z3,z5,z6])],[(0,[z0,z1,z2,z266,z18,z6]),(0,[z0,z23,z25,z3,z5,z6]),(0,[z0,z1,z945,z3,z5,z6]),(0,[z0,z1,z2,z3,z946,z6])],[(0,[z0,z1,z2,z947,z5,z6]),(0,[z109,z0,z1,z539,z3,z6]),(0,[z0,z1,z2,z268,z18,z6]),(0,[z0,z23,z2,z165,z5,z6]),(0,[z0,z284,z2,z51,z3,z6]),(0,[z948,z1,z2,z3,z5,z6])],[(0,[z0,z166,z2,z3,z7,z6]),(0,[z609,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z949,z6]),(0,[z0,z25,z3,z5,z6,z31]),(0,[z0,z1,z505,z3,z22,z6])],[(0,[z354,z0,z1,z3,z5,z117]),(0,[z0,z23,z2,z165,z18,z6]),(0,[z0,z1,z149,z3,z6,z37])],[(0,[z1,z102,z2,z3,z395,z6]),(0,[z0,z1,z2,z950,z5,z6]),(0,[z0,z951,z1,z2,z3,z6]),(0,[z0,z1,z952,z3,z5,z6]),(0,[z917,z88,z1,z2,z3,z6])],[(0,[z127,z102,z2,z3,z7,z6]),(0,[z0,z953,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z954,z6]),(0,[z0,z955,z2,z3,z5,z6]),(0,[z0,z24,z956,z2,z3,z6])],[(0,[z560,z102,z2,z3,z5,z6]),(0,[z102,z2,z3,z7,z6,z31]),(0,[z0,z957,z1,z2,z3,z6]),(0,[z263,z1,z2,z3,z7,z6]),(0,[z0,z23,z2,z51,z165,z6]),(0,[z1,z2,z3,z5,z6,z958]),(0,[z0,z1,z2,z3,z959,z6])],[(0,[z0,z1,z2,z3,z960,z6]),(0,[z0,z1,z2,z3,z961,z6]),(0,[z0,z1,z2,z3,z962,z6]),(0,[z0,z24,z1,z2,z321,z6]),(0,[z56,z0,z1,z51,z3,z117]),(0,[z0,z1,z2,z3,z963,z6]),(0,[z0,z1,z2,z5,z964,z26])],[(0,[z0,z1,z2,z3,z965,z6]),(0,[z0,z966,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z967,z6]),(0,[z0,z262,z2,z51,z3,z6]),(0,[z0,z24,z1,z2,z548,z6])],[(0,[z0,z968,z1,z2,z3,z6]),(0,[z0,z969,z2,z3,z5,z6]),(0,[z0,z1,z467,z3,z6,z37]),(0,[z0,z1,z2,z3,z970,z6]),(0,[z648,z0,z141,z3,z5,z6]),(0,[z0,z1,z2,z971,z3,z6]),(0,[z0,z1,z2,z573,z6,z37])],[(0,[z85,z1,z2,z3,z140,z6]),(0,[z260,z1,z2,z3,z138,z6])],[(0,[z137,z1,z2,z3,z281,z6]),(0,[z0,z306,z131,z3,z5,z6]),(0,[z0,z1,z44,z2,z7,z26]),(0,[z0,z1,z2,z3,z972,z6]),(0,[z0,z1,z2,z3,z114,z6])],[(0,[z0,z973,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z140,z6]),(0,[z0,z1,z363,z2,z6,z26]),(0,[z0,z1,z571,z3,z6,z37])],[(0,[z102,z2,z122,z3,z7,z6]),(0,[z0,z974,z2,z3,z5,z6]),(0,[z1,z932,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z975,z6]),(0,[z0,z1,z2,z3,z976,z6])]],
   [[(0,[z0,z1,z2,z3,z977,z6]),(0,[z0,z978,z1,z2,z3,z6]),(0,[z0,z430,z2,z3,z43,z6]),(0,[z0,z2,z3,z5,z6,z979])],[(0,[z0,z1,z2,z980,z3,z6]),(0,[z70,z0,z2,z3,z7,z31]),(0,[z0,z981,z2,z3,z5,z6]),(0,[z0,z359,z2,z3,z214,z6])],[(0,[z0,z1,z2,z3,z128,z6]),(0,[z0,z982,z1,z2,z3,z6]),(0,[z90,z1,z107,z3,z5,z6]),(0,[z1,z2,z3,z544,z18,z6]),(0,[z0,z1,z86,z104,z5,z6]),(0,[z0,z1,z48,z573,z5,z6]),(0,[z917,z24,z1,z2,z3,z6])],[(0,[z1,z153,z500,z3,z5,z6]),(0,[z0,z1,z2,z3,z983,z6]),(0,[z0,z1,z2,z984,z3,z6]),(0,[z0,z1,z985,z3,z5,z6]),(0,[z0,z1,z2,z3,z986,z6])],[(0,[z0,z1,z2,z987,z5,z6]),(0,[z0,z1,z2,z988,z5,z6]),(0,[z989,z1,z2,z3,z5,z6]),(0,[z64,z1,z2,z3,z990,z6]),(0,[z0,z24,z1,z2,z6,z219]),(0,[z0,z1,z991,z51,z3,z6]),(0,[z0,z1,z51,z3,z6,z442])],[(0,[z109,z24,z1,z153,z3,z6]),(0,[z0,z1,z149,z3,z212,z6]),(0,[z0,z1,z2,z3,z992,z6]),(0,[z56,z0,z430,z3,z5,z117])],[(0,[z0,z1,z2,z988,z18,z6]),(0,[z0,z993,z1,z2,z3,z6]),(0,[z121,z0,z141,z3,z138,z6]),(0,[z64,z1,z2,z3,z994,z6])],[(0,[z295,z1,z2,z3,z7,z6]),(0,[z175,z1,z153,z3,z5,z6]),(0,[z0,z1,z283,z51,z3,z6]),(0,[z0,z1,z2,z3,z6,z995]),(0,[z260,z1,z2,z51,z3,z6]),(0,[z0,z1,z2,z3,z996,z6])],[(0,[z0,z1,z2,z3,z997,z6]),(0,[z998,z1,z2,z3,z5,z6]),(0,[z999,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1000,z6])],[(0,[z0,z1,z2,z332,z5,z6]),(0,[z0,z1,z133,z3,z22,z6]),(0,[z0,z1,z508,z55,z2,z6]),(0,[z0,z24,z2,z3,z6,z100])],[(0,[z0,z1,z1001,z2,z3,z6]),(0,[z0,z1,z505,z3,z7,z6]),(0,[z0,z1,z2,z3,z1002,z6]),(0,[z0,z1,z1003,z2,z3,z6]),(0,[z0,z359,z2,z165,z5,z6]),(0,[z0,z1,z3,z493,z6,z37])],[(0,[z1,z339,z2,z3,z5,z6]),(0,[z0,z1,z2,z1004,z3,z6]),(0,[z0,z1,z2,z332,z18,z6]),(0,[z0,z1,z2,z3,z6,z1005]),(0,[z0,z1,z2,z466,z6,z37])],[(0,[z1006,z24,z1,z2,z3,z6])],[(0,[z0,z24,z306,z2,z3,z6]),(0,[z1,z339,z2,z3,z18,z6]),(0,[z0,z1007,z1,z2,z3,z6]),(0,[z56,z0,z1,z57,z5,z117])],[(0,[z0,z1,z2,z57,z7,z6]),(0,[z0,z24,z1,z2,z445,z6]),(0,[z0,z1,z2,z3,z6,z1008]),(0,[z1009,z1,z2,z3,z5,z6]),(0,[z64,z1,z2,z3,z22,z6])],[(0,[z0,z415,z2,z3,z6,z37]),(0,[z81,z0,z1,z55,z2,z6]),(0,[z0,z24,z166,z2,z3,z6]),(0,[z0,z1,z1010,z2,z3,z6]),(0,[z14,z1,z2,z3,z518,z6])]],
   [[(0,[z1,z1011,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1012,z6]),(0,[z0,z1,z141,z3,z6,z245]),(0,[z0,z1013,z2,z3,z5,z6]),(0,[z1,z2,z328,z3,z7,z6])],[(0,[z121,z0,z141,z51,z3,z6]),(0,[z0,z1,z3,z5,z6,z1014]),(0,[z0,z24,z1,z1015,z3,z6]),(0,[z1016,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1017,z6])],[(0,[z0,z1,z2,z3,z1018,z6]),(0,[z0,z1,z2,z3,z5,z1019]),(0,[z1,z2,z3,z18,z140,z6]),(0,[z0,z430,z2,z3,z599,z6]),(0,[z0,z1,z3,z518,z6,z442])],[(0,[z0,z1,z141,z3,z6,z217]),(0,[z0,z1,z86,z51,z3,z6]),(0,[z288,z1,z2,z3,z6,z37]),(0,[z0,z1,z130,z161,z6,z37]),(0,[z0,z1,z2,z3,z1020,z6])],[(0,[z0,z125,z1,z2,z3,z6]),(0,[z0,z494,z2,z3,z93,z6]),(0,[z377,z1,z2,z51,z3,z6]),(0,[z1,z2,z3,z6,z37,z111])],[(0,[z0,z1,z2,z1021,z5,z6]),(0,[z0,z1,z2,z3,z1022,z6]),(0,[z0,z1,z508,z141,z3,z6]),(0,[z295,z1,z2,z3,z174,z6]),(0,[z0,z1,z116,z133,z3,z6]),(0,[z0,z24,z1,z2,z51,z6]),(0,[z1,z44,z2,z5,z111,z26])],[(0,[z0,z1,z2,z1023,z3,z6]),(0,[z0,z1,z2,z104,z22,z6]),(0,[z0,z1,z2,z3,z1024,z6])],[(0,[z0,z1,z2,z3,z6,z113]),(0,[z0,z1,z2,z332,z256,z6]),(0,[z1,z2,z3,z5,z6,z1025]),(0,[z0,z1,z2,z3,z6,z1026])],[(0,[z0,z1027,z1,z2,z3,z6]),(0,[z0,z369,z1,z2,z6,z26])],[(0,[z0,z1,z222,z3,z461,z6]),(0,[z0,z494,z2,z3,z5,z6]),(0,[z0,z1,z2,z1028,z5,z6]),(0,[z0,z1,z2,z3,z1029,z6])],[(0,[z0,z1,z2,z3,z1030,z6]),(0,[z473,z125,z1,z2,z3,z6]),(0,[z0,z1,z3,z6,z551,z37]),(0,[z0,z1,z2,z3,z6,z1031]),(0,[z0,z1,z2,z1032,z5,z6]),(0,[z185,z1,z2,z3,z6,z37])],[(0,[z0,z1,z251,z51,z3,z6]),(0,[z0,z1,z107,z3,z7,z6]),(0,[z0,z262,z107,z3,z5,z6]),(0,[z0,z1,z2,z3,z6,z1033]),(0,[z0,z1,z2,z3,z1034,z6])],[(0,[z0,z24,z1,z628,z2,z6]),(0,[z0,z1,z2,z1035,z3,z6]),(0,[z782,z1,z2,z3,z5,z6]),(0,[z377,z2,z122,z3,z5,z6]),(0,[z0,z1,z2,z3,z6,z1036]),(0,[z0,z1,z465,z3,z22,z6])],[(0,[z0,z24,z1,z209,z2,z6])],[(0,[z0,z53,z1,z101,z2,z6])],[(0,[z0,z1,z2,z3,z785,z6]),(0,[z0,z1,z133,z3,z7,z6])]],
   [[(0,[z0,z102,z141,z3,z6,z37]),(0,[z0,z1,z1037,z3,z5,z6]),(0,[z0,z1,z2,z3,z1038,z6]),(0,[z0,z1,z149,z51,z3,z6]),(0,[z0,z166,z2,z573,z5,z6])],[(0,[z1011,z102,z2,z3,z5,z6])],[],[(0,[z0,z156,z2,z3,z280,z6]),(0,[z0,z1,z2,z445,z36,z6]),(0,[z0,z1039,z1,z2,z3,z6]),(0,[z603,z1,z2,z3,z1040,z6])],[(0,[z0,z1,z222,z3,z5,z6]),(1,[z102,z251,z3,z5,z6]),(0,[z137,z1,z2,z374,z3,z6]),(0,[z0,z1041,z1,z2,z3,z6]),(0,[z0,z24,z1,z467,z3,z6]),(0,[z0,z1,z2,z3,z1042,z6]),(0,[z64,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z463,z80]),(0,[z0,z20,z141,z3,z6,z37]),(0,[z0,z1,z2,z3,z1043,z6]),(0,[z0,z24,z202,z2,z3,z6]),(0,[z0,z2,z3,z6,z37,z100])],[(0,[z0,z1,z2,z3,z1044,z6]),(0,[z0,z1,z2,z3,z1045,z6])],[(0,[z0,z1,z222,z3,z18,z6]),(0,[z125,z1,z131,z2,z3,z6]),(0,[z0,z1,z467,z51,z3,z6]),(0,[z1,z383,z2,z3,z7,z6]),(0,[z0,z1,z20,z3,z273,z6]),(0,[z0,z1,z2,z1046,z3,z6]),(0,[z0,z1,z2,z3,z6,z1047]),(0,[z0,z1,z1048,z2,z3,z6]),(0,[z0,z1,z1049,z3,z5,z6]),(0,[z0,z88,z1,z2,z6,z26]),(0,[z0,z1,z44,z2,z214,z26])],[(0,[z0,z1,z2,z3,z1050,z6]),(0,[z0,z1,z2,z3,z1051,z6]),(0,[z0,z774,z1,z2,z332,z6]),(0,[z0,z1,z2,z3,z1052,z6]),(0,[z0,z1,z48,z539,z3,z6]),(0,[z0,z1,z3,z22,z6,z37]),(0,[z661,z0,z1,z3,z6,z37]),(0,[z546,z1,z2,z3,z140,z6]),(0,[z0,z1,z1053,z2,z3,z79])],[(0,[z0,z1,z2,z3,z5,z1054]),(0,[z0,z306,z153,z3,z5,z6]),(0,[z0,z1,z2,z3,z1055,z6]),(0,[z0,z1,z2,z3,z366,z6]),(0,[z0,z1056,z2,z3,z5,z6]),(0,[z1057,z1,z2,z3,z5,z6])],[(0,[z0,z1,z1058,z3,z5,z6]),(0,[z0,z1,z1059,z2,z3,z6]),(0,[z181,z1,z2,z3,z7,z6]),(0,[z0,z2,z3,z5,z936,z31]),(0,[z0,z1,z2,z3,z6,z1060]),(0,[z64,z24,z1,z2,z3,z6]),(0,[z24,z1,z2,z6,z111,z26])],[(0,[z0,z1,z2,z1061,z3,z6]),(0,[z0,z1,z2,z3,z1062,z6]),(0,[z0,z1,z1063,z2,z7,z6]),(0,[z0,z498,z2,z3,z366,z6]),(0,[z355,z0,z141,z3,z5,z6]),(0,[z0,z1,z2,z3,z1064,z6])],[(0,[z0,z1,z885,z2,z3,z6]),(0,[z181,z1,z2,z3,z853,z6]),(0,[z0,z1065,z1,z2,z3,z6]),(0,[z0,z23,z2,z268,z5,z6]),(0,[z0,z24,z1,z2,z501,z6]),(0,[z14,z1,z2,z3,z214,z6])],[(0,[z0,z1,z2,z3,z6,z1066]),(0,[z0,z1,z2,z104,z7,z6]),(0,[z0,z1,z1067,z2,z5,z6]),(0,[z85,z1,z2,z3,z5,z75]),(0,[z0,z262,z2,z104,z5,z6]),(0,[z0,z1,z2,z3,z1068,z6]),(0,[z0,z23,z1,z55,z2,z6]),(0,[z0,z1,z1069,z3,z5,z6])],[(0,[z0,z1,z700,z2,z5,z26]),(0,[z0,z1,z133,z3,z174,z6]),(0,[z0,z284,z2,z3,z357,z6]),(0,[z0,z430,z3,z5,z6,z117])],[(0,[z594,z102,z2,z3,z5,z6]),(0,[z0,z1070,z2,z3,z5,z6]),(0,[z0,z1071,z1,z2,z3,z6]),(0,[z1,z2,z3,z5,z6,z111]),(0,[z85,z1,z2,z3,z18,z75]),(0,[z0,z1,z1067,z2,z18,z6]),(0,[z418,z0,z1,z3,z6,z37]),(0,[z70,z0,z2,z3,z22,z31])],[(0,[z0,z1,z2,z1072,z3,z6])]],
   [[(0,[z0,z1,z2,z3,z1073,z6]),(0,[z0,z430,z2,z3,z5,z6]),(0,[z0,z1074,z2,z3,z5,z6]),(0,[z0,z1,z136,z101,z2,z6])],[(0,[z0,z1,z2,z3,z280,z6]),(0,[z90,z1,z2,z51,z177,z6]),(0,[z90,z0,z1,z55,z2,z6]),(0,[z0,z1,z2,z3,z1075,z6]),(0,[z0,z1076,z1,z2,z3,z6])],[(0,[z0,z369,z1,z34,z2,z6]),(0,[z1,z2,z3,z7,z6,z111]),(0,[z675,z1,z2,z3,z7,z6]),(0,[z0,z430,z2,z3,z18,z6]),(0,[z0,z1,z2,z1077,z5,z6]),(0,[z0,z24,z1,z2,z6,z26]),(0,[z0,z24,z1,z1078,z3,z6])],[(0,[z0,z1,z2,z3,z1079,z6]),(0,[z0,z1,z1080,z2,z3,z6]),(0,[z0,z1,z2,z3,z889,z6]),(0,[z0,z1,z2,z3,z6,z1081])],[(0,[z0,z24,z1,z817,z3,z6])],[(0,[z0,z1,z2,z1082,z3,z6]),(0,[z0,z23,z363,z2,z165,z6]),(0,[z0,z1,z3,z358,z6,z37]),(0,[z0,z325,z2,z3,z493,z6])],[(0,[z235,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z1083,z3,z6]),(0,[z0,z1,z237,z2,z5,z26])],[(0,[z1,z420,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z212,z6]),(0,[z0,z1,z2,z3,z5,z748])],[(0,[z147,z1,z2,z3,z1084,z6]),(0,[z0,z1,z20,z3,z6,z37]),(0,[z1085,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z964])],[(0,[z0,z306,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z272,z6]),(0,[z0,z415,z2,z51,z3,z6]),(0,[z85,z1,z2,z3,z256,z75])],[(0,[z0,z306,z2,z3,z18,z6]),(0,[z368,z1,z2,z3,z18,z6]),(0,[z0,z1,z2,z1086,z3,z6]),(0,[z0,z147,z141,z3,z5,z6]),(0,[z252,z1,z2,z3,z22,z6]),(0,[z0,z24,z1,z620,z2,z6]),(0,[z0,z1,z2,z57,z22,z6])],[(0,[z0,z1,z2,z3,z1087,z6])],[(0,[z1,z2,z199,z36,z3,z6]),(0,[z0,z1,z2,z5,z1088,z6]),(0,[z0,z1,z2,z321,z3,z6])],[(0,[z603,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z6,z1089]),(0,[z147,z1,z2,z3,z22,z6]),(0,[z0,z1,z506,z3,z6,z37]),(0,[z288,z1,z2,z51,z3,z6])],[(0,[z0,z1,z3,z1090,z6,z37]),(0,[z0,z1,z2,z3,z1091,z6]),(0,[z1092,z1,z2,z3,z5,z6]),(0,[z185,z166,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z1093,z3,z5,z6]),(0,[z0,z1,z2,z3,z411,z6]),(0,[z0,z88,z1,z34,z2,z6]),(0,[z0,z1,z101,z2,z51,z6])],[(0,[z0,z1,z1094,z3,z5,z6]),(0,[z10,z295,z2,z3,z11,z6]),(0,[z0,z1095,z2,z3,z5,z6])],[(0,[z0,z2,z3,z7,z6,z100]),(0,[z0,z1,z2,z3,z1096,z6]),(0,[z488,z1,z2,z3,z1097,z6]),(0,[z603,z202,z2,z3,z5,z6])],[(0,[z0,z1,z1098,z2,z3,z6])],[(0,[z0,z1,z2,z3,z1099,z6]),(0,[z127,z102,z2,z3,z461,z6]),(0,[z1100,z0,z1,z3,z5,z6]),(0,[z0,z1,z505,z3,z1101,z6])],[(0,[z0,z1,z2,z3,z1102,z6]),(0,[z0,z1,z55,z141,z3,z6]),(0,[z0,z1,z2,z3,z1103,z6]),(0,[z1,z1104,z2,z3,z22,z6]),(0,[z185,z1,z2,z51,z3,z6]),(0,[z0,z1,z1053,z2,z3,z80])],[(0,[z0,z1,z2,z3,z1105,z6]),(0,[z0,z1106,z1,z2,z3,z6]),(0,[z0,z24,z1,z135,z2,z6])],[(0,[z0,z1,z2,z3,z1107,z6]),(0,[z0,z1,z1108,z3,z5,z6]),(0,[z0,z1,z1109,z3,z5,z6]),(0,[z0,z1,z141,z3,z273,z6]),(0,[z0,z1,z1110,z3,z5,z6]),(0,[z1111,z1,z2,z3,z22,z6]),(0,[z0,z44,z2,z5,z100,z26]),(0,[z0,z1,z135,z101,z2,z6])],[(0,[z137,z1,z2,z3,z7,z6]),(0,[z90,z1,z2,z532,z5,z6]),(0,[z0,z1,z2,z3,z1112,z6]),(0,[z0,z1,z107,z3,z22,z6]),(0,[z0,z1,z2,z3,z1113,z6]),(0,[z0,z1,z2,z3,z1114,z6]),(0,[z0,z1,z2,z3,z1115,z6]),(0,[z0,z1,z1116,z3,z5,z6])],[(0,[z0,z1,z153,z3,z6,z113]),(0,[z0,z1,z141,z3,z6,z113]),(0,[z0,z284,z2,z3,z22,z6])],[(0,[z90,z415,z2,z3,z5,z6]),(0,[z0,z1,z1117,z2,z5,z6]),(0,[z0,z1,z2,z3,z1118,z6]),(0,[z0,z1,z1119,z2,z3,z6])],[(0,[z1,z102,z2,z3,z6,z245]),(0,[z0,z1,z2,z3,z1120,z6]),(0,[z0,z1121,z1,z2,z3,z6]),(0,[z0,z2,z1122,z165,z5,z6])],[(0,[z0,z1,z1123,z3,z7,z6]),(0,[z235,z1,z2,z3,z7,z6]),(0,[z0,z1,z130,z573,z5,z6]),(0,[z1124,z1,z2,z3,z5,z6]),(0,[z0,z24,z1,z34,z2,z6]),(0,[z0,z1,z2,z3,z79,z299])],[(0,[z90,z262,z2,z3,z5,z6]),(0,[z0,z1,z1125,z2,z3,z6]),(0,[z0,z1,z44,z2,z518,z26])],[(0,[z0,z1,z1126,z3,z5,z6]),(0,[z0,z1127,z1,z2,z3,z6]),(0,[z0,z1,z2,z1128,z3,z6]),(0,[z0,z1,z2,z1129,z5,z6]),(0,[z0,z24,z430,z2,z3,z6])],[(0,[z137,z216,z2,z3,z7,z6]),(0,[z0,z1130,z2,z3,z5,z6]),(0,[z478,z1,z2,z3,z18,z6]),(0,[z121,z147,z141,z3,z5,z6]),(0,[z70,z0,z2,z3,z30,z31]),(0,[z56,z0,z1,z3,z22,z117]),(0,[z1131,z24,z1,z2,z3,z6])]],
   [[(0,[z0,z2,z3,z872,z11,z6]),(0,[z70,z0,z2,z3,z5,z936]),(0,[z64,z1,z2,z573,z5,z6]),(0,[z0,z24,z1,z155,z3,z6])],[(0,[z252,z1,z2,z3,z7,z6]),(0,[z84,z1,z2,z3,z853,z6]),(0,[z235,z24,z1,z2,z3,z6]),(0,[z56,z0,z1,z3,z5,z1132]),(0,[z1133,z24,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z1134,z6]),(1,[z0,z1,z885,z2,z6]),(0,[z0,z1,z2,z3,z6,z1135])],[(0,[z0,z1,z101,z2,z5,z6])],[(0,[z0,z1,z1136,z3,z5,z6]),(0,[z0,z473,z1,z2,z3,z6]),(0,[z147,z1,z2,z3,z7,z6]),(0,[z0,z429,z1,z2,z6,z26]),(0,[z0,z24,z1,z2,z6,z433])],[(0,[z0,z1,z101,z2,z18,z6])],[(0,[z127,z1011,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1137,z6]),(0,[z85,z1,z2,z332,z5,z75]),(0,[z252,z24,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1138,z6]),(0,[z0,z1,z44,z2,z5,z964])],[(0,[z0,z24,z1,z2,z651,z6]),(0,[z0,z1,z2,z3,z1139,z6]),(0,[z0,z1,z48,z2,z321,z6])],[(0,[z91,z1,z131,z3,z7,z6]),(0,[z81,z1,z2,z36,z7,z6]),(0,[z0,z1,z2,z3,z273,z6])],[(0,[z0,z1,z1140,z3,z5,z6]),(0,[z147,z24,z1,z2,z3,z6]),(0,[z185,z1,z2,z57,z5,z6])],[(0,[z14,z1,z2,z3,z5,z6]),(0,[z90,z1,z2,z177,z6,z37]),(0,[z0,z1,z2,z3,z1141,z6]),(0,[z70,z0,z154,z2,z3,z31]),(0,[z0,z1,z155,z161,z5,z6])],[(0,[z488,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1142,z6]),(0,[z0,z1,z2,z3,z6,z1143]),(0,[z0,z1,z363,z34,z2,z6]),(0,[z0,z1,z1144,z2,z3,z6]),(0,[z0,z1,z2,z3,z66,z6])],[(0,[z102,z2,z232,z3,z5,z6]),(0,[z0,z1,z2,z1145,z5,z6]),(0,[z14,z1,z2,z3,z18,z6]),(0,[z0,z1,z2,z3,z1146,z6]),(0,[z0,z1,z25,z3,z411,z6]),(0,[z1147,z1,z2,z3,z6,z37])],[(0,[z0,z1,z2,z3,z6,z1148]),(0,[z0,z1149,z1,z2,z3,z6]),(0,[z0,z1,z283,z3,z22,z6]),(0,[z1,z649,z2,z3,z7,z6]),(0,[z488,z1,z2,z3,z18,z6]),(0,[z260,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z3,z1150,z6])],[(0,[z0,z1,z2,z832,z5,z6]),(0,[z0,z494,z2,z3,z18,z6]),(0,[z64,z1,z2,z3,z599,z6]),(0,[z0,z1,z2,z3,z1151,z6])],[(0,[z0,z1,z1152,z3,z5,z6]),(0,[z0,z1,z2,z3,z1153,z6]),(0,[z0,z284,z2,z3,z7,z6]),(0,[z0,z1,z2,z1154,z3,z6]),(0,[z0,z1,z2,z1155,z3,z6]),(0,[z0,z1,z2,z3,z6,z1156]),(0,[z0,z1,z130,z51,z161,z6]),(0,[z603,z1,z2,z3,z54,z6]),(0,[z0,z166,z2,z3,z43,z6])]],
   [[(0,[z109,z156,z153,z3,z5,z6]),(0,[z0,z1,z2,z3,z1157,z6]),(0,[z0,z1,z2,z3,z1158,z6])],[(0,[z0,z1,z2,z3,z6,z1159])],[],[(0,[z59,z0,z1,z3,z6,z113]),(0,[z0,z1160,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z6,z1161])],[(0,[z1,z102,z2,z3,z272,z6]),(0,[z0,z1162,z2,z3,z5,z6]),(0,[z0,z494,z2,z3,z344,z6]),(0,[z0,z1,z2,z3,z1163,z6]),(0,[z0,z1,z195,z3,z6,z37]),(0,[z0,z1,z3,z5,z6,z1164]),(0,[z0,z1165,z1,z2,z3,z6]),(0,[z0,z359,z155,z3,z5,z6])],[(0,[z56,z0,z1,z3,z7,z117]),(0,[z295,z1,z2,z3,z668,z6])],[(0,[z1166,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z265,z3,z6]),(0,[z0,z1,z149,z3,z1167,z6]),(0,[z1168,z1,z2,z3,z5,z6]),(0,[z0,z1,z1169,z3,z5,z6])],[(0,[z0,z1,z2,z3,z1170,z6]),(0,[z0,z1,z3,z7,z6,z442]),(0,[z121,z0,z141,z3,z22,z6]),(0,[z0,z1,z2,z3,z6,z1171]),(0,[z0,z1,z2,z3,z5,z1132])],[(0,[z1172,z1,z2,z3,z5,z6])],[(0,[z137,z1,z251,z3,z5,z6]),(0,[z0,z1,z2,z3,z1173,z6]),(0,[z0,z1,z86,z3,z22,z6]),(0,[z0,z2,z739,z3,z5,z6])],[(0,[z0,z1,z2,z3,z6,z37]),(0,[z377,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z904,z6,z37]),(0,[z0,z24,z1,z804,z3,z6])],[(0,[z1,z102,z2,z3,z140,z6]),(0,[z0,z1,z2,z1174,z3,z6]),(0,[z0,z24,z1,z86,z3,z6]),(0,[z0,z1,z2,z1175,z3,z6]),(0,[z0,z1,z1176,z3,z5,z6])],[(0,[z0,z1177,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z6,z1178]),(0,[z0,z498,z2,z3,z6,z37]),(0,[z1,z2,z3,z140,z8,z6]),(0,[z1179,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z1180,z5,z6]),(0,[z0,z1,z2,z3,z823,z6]),(0,[z1,z683,z2,z3,z7,z6]),(0,[z488,z1,z2,z268,z5,z6])],[(0,[z1,z2,z3,z1134,z7,z6]),(0,[z109,z1,z153,z3,z5,z6]),(0,[z0,z1,z2,z1181,z3,z6]),(0,[z0,z1,z2,z1182,z5,z6]),(0,[z0,z1,z2,z1183,z5,z6]),(0,[z0,z429,z1,z34,z2,z6]),(0,[z0,z202,z2,z3,z6,z37]),(0,[z0,z24,z1,z101,z2,z6])],[(0,[z1,z102,z2,z3,z128,z6]),(0,[z0,z1,z2,z3,z1184,z6]),(0,[z0,z1,z885,z2,z7,z6])]],
   [[(0,[z0,z1,z2,z1185,z5,z6]),(0,[z109,z1,z153,z3,z18,z6]),(0,[z0,z1,z2,z3,z1186,z6]),(0,[z0,z1,z2,z3,z1187,z6]),(0,[z0,z141,z3,z6,z572,z37]),(0,[z0,z1,z1188,z3,z5,z6])],[(0,[z0,z1,z251,z3,z22,z6]),(0,[z0,z1,z130,z539,z3,z6]),(0,[z0,z166,z2,z3,z599,z6])],[(0,[z0,z1,z2,z3,z1189,z6]),(0,[z0,z1,z2,z3,z6,z1190]),(0,[z0,z1,z1191,z3,z5,z6])],[(0,[z0,z1,z283,z3,z7,z6]),(0,[z260,z1,z2,z3,z7,z6]),(0,[z0,z1,z1192,z3,z7,z6]),(0,[z0,z1,z1193,z3,z5,z6]),(0,[z0,z1,z2,z3,z1194,z6]),(0,[z0,z359,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1195,z6])],[(0,[z0,z1196,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1197,z6]),(0,[z0,z1,z195,z3,z212,z6]),(0,[z0,z10,z2,z3,z11,z6]),(0,[z298,z1,z2,z3,z6,z245])],[(0,[z0,z1,z2,z3,z1198,z6]),(0,[z0,z1,z2,z3,z19,z6]),(0,[z0,z359,z2,z3,z18,z6]),(0,[z0,z1,z1193,z3,z18,z6]),(0,[z0,z1,z2,z1086,z332,z6]),(0,[z0,z202,z48,z3,z5,z6]),(0,[z0,z1007,z1,z2,z573,z6]),(0,[z359,z2,z3,z5,z6,z111])],[(0,[z0,z1,z2,z1199,z5,z6]),(0,[z288,z1,z2,z3,z1200,z6]),(0,[z0,z1,z2,z1201,z3,z6]),(0,[z0,z1202,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z1203,z6]),(0,[z0,z1,z2,z3,z1204,z6]),(0,[z488,z1,z25,z3,z5,z6]),(0,[z0,z1,z2,z3,z1205,z6]),(0,[z0,z1,z2,z3,z1206,z6])],[(0,[z0,z1,z251,z3,z6,z1207]),(0,[z0,z1,z2,z3,z5,z1208]),(0,[z91,z1,z2,z3,z6,z226]),(0,[z260,z24,z1,z2,z3,z6]),(0,[z1209,z1,z2,z3,z5,z6]),(0,[z0,z1,z539,z3,z6,z117])],[(0,[z0,z1,z2,z1210,z5,z6]),(0,[z90,z1,z467,z3,z5,z6]),(0,[z0,z1,z2,z3,z1211,z6]),(0,[z1,z339,z2,z3,z1002,z6]),(0,[z0,z1,z2,z57,z43,z6])],[(0,[z125,z1,z2,z36,z3,z6]),(0,[z0,z1,z2,z3,z1212,z6]),(0,[z0,z24,z1,z34,z2,z299])],[(0,[z0,z1,z3,z395,z6,z37]),(0,[z1213,z1,z2,z3,z5,z6]),(0,[z0,z1214,z2,z3,z5,z6])],[(0,[z0,z1,z251,z3,z1215,z6]),(0,[z0,z1216,z2,z3,z5,z6]),(0,[z0,z1,z1217,z2,z3,z6]),(0,[z0,z202,z130,z3,z5,z6])],[(0,[z90,z1,z2,z365,z177,z6]),(0,[z121,z0,z141,z3,z7,z6]),(0,[z0,z1,z1218,z2,z5,z6]),(0,[z1219,z1,z2,z3,z22,z6]),(0,[z0,z1220,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z1221,z6]),(0,[z0,z369,z1,z130,z2,z6]),(0,[z0,z23,z2,z165,z6,z37]),(0,[z0,z1,z2,z539,z6,z26])],[(0,[z0,z1,z86,z3,z7,z6]),(0,[z0,z262,z86,z3,z5,z6]),(0,[z24,z377,z1,z2,z3,z6]),(0,[z1222,z1,z2,z3,z5,z6]),(0,[z1223,z1,z2,z3,z5,z6]),(0,[z0,z1,z1224,z2,z3,z6])]],
   [[(0,[z0,z23,z369,z1,z2,z6]),(0,[z377,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z1225,z5,z6]),(0,[z64,z1,z71,z3,z5,z6])],[(1,[z1,z2,z3,z853,z6]),(0,[z1,z2,z3,z7,z196,z6]),(0,[z0,z1,z2,z3,z6,z1226]),(0,[z0,z1,z2,z3,z79,z515]),(0,[z0,z1,z83,z3,z5,z6]),(0,[z1227,z1,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z6,z100]),(0,[z0,z2,z3,z5,z6,z1228])],[(0,[z0,z1,z1229,z3,z5,z6]),(0,[z0,z1,z2,z3,z1230,z6]),(0,[z1231,z1,z2,z3,z5,z6]),(0,[z142,z1,z2,z3,z6,z226])],[(0,[z0,z1,z2,z3,z1232,z6]),(0,[z0,z1,z1233,z2,z3,z6]),(0,[z0,z1,z817,z36,z3,z6]),(0,[z0,z1,z2,z3,z1234,z6]),(0,[z603,z1,z2,z3,z18,z6]),(0,[z0,z1,z83,z3,z18,z6])],[(0,[z0,z1,z2,z3,z1235,z6]),(0,[z0,z1,z3,z5,z6,z1236])],[(0,[z295,z1,z116,z2,z3,z6]),(0,[z0,z359,z2,z268,z5,z6]),(0,[z0,z1237,z2,z3,z5,z6]),(0,[z870,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z1238,z5,z6]),(0,[z0,z1,z44,z2,z51,z26])],[(0,[z0,z1,z1239,z3,z5,z6]),(0,[z0,z1,z1240,z3,z5,z6]),(0,[z0,z1,z2,z3,z6,z1241]),(0,[z0,z1,z2,z3,z1242,z6]),(0,[z0,z498,z2,z104,z5,z6]),(0,[z0,z1,z25,z3,z6,z37])],[(0,[z0,z1,z251,z3,z7,z6]),(0,[z14,z1,z2,z36,z5,z6]),(0,[z1243,z1,z2,z3,z5,z6]),(0,[z0,z1,z20,z3,z1090,z6]),(0,[z1244,z1,z2,z3,z5,z6]),(0,[z0,z1,z1245,z51,z3,z6])],[(0,[z0,z1,z2,z3,z1246,z6]),(0,[z0,z1,z1240,z3,z18,z6]),(0,[z0,z1,z1247,z2,z3,z6])],[(0,[z0,z1,z2,z3,z1248,z6])],[(0,[z0,z1,z222,z3,z128,z6]),(0,[z692,z0,z141,z3,z5,z6]),(0,[z1,z2,z153,z3,z6,z226]),(0,[z1249,z1,z2,z3,z5,z6])],[(0,[z0,z306,z2,z3,z280,z6]),(0,[z0,z1,z2,z57,z599,z6]),(0,[z0,z1,z2,z3,z1250,z6])],[(0,[z0,z1,z2,z3,z1251,z6]),(0,[z0,z1,z1252,z3,z5,z6]),(0,[z76,z125,z1,z2,z3,z6]),(0,[z0,z1,z2,z1253,z5,z6]),(0,[z0,z1,z2,z466,z22,z6]),(0,[z0,z1,z852,z3,z6,z442])],[(0,[z137,z1,z2,z3,z395,z6]),(0,[z1,z107,z3,z5,z6,z75]),(0,[z0,z665,z141,z3,z5,z6]),(0,[z0,z1,z2,z3,z1254,z6]),(0,[z0,z1,z1255,z2,z3,z6]),(0,[z0,z1,z2,z3,z6,z1256])],[(0,[z70,z0,z2,z3,z5,z422]),(0,[z0,z1,z133,z3,z183,z6]),(0,[z14,z1,z155,z3,z5,z6])],[(0,[z0,z1,z2,z3,z285,z515]),(0,[z0,z166,z2,z3,z5,z6]),(0,[z0,z1,z55,z2,z161,z6]),(0,[z64,z1,z2,z3,z43,z6])]],
   [[(0,[z0,z1,z2,z3,z1257,z6]),(0,[z0,z1,z2,z3,z1258,z6]),(0,[z0,z415,z2,z3,z22,z6]),(0,[z0,z1,z2,z3,z1259,z6]),(0,[z0,z1,z2,z3,z1260,z6]),(0,[z870,z1,z48,z2,z3,z6])],[(0,[z0,z1,z2,z3,z1261,z6]),(0,[z0,z416,z2,z3,z11,z6]),(0,[z0,z166,z2,z3,z18,z6]),(0,[z0,z1,z2,z3,z6,z1262]),(0,[z56,z0,z1,z573,z5,z117]),(0,[z24,z870,z1,z2,z3,z6])],[(0,[z127,z102,z2,z3,z5,z6]),(0,[z0,z1,z467,z3,z7,z6]),(0,[z0,z1,z2,z3,z1263,z6]),(0,[z0,z1,z2,z104,z256,z6]),(0,[z0,z1,z2,z3,z1264,z6])],[(0,[z0,z1,z2,z3,z1265,z6]),(0,[z0,z262,z2,z3,z22,z6]),(0,[z1266,z1,z2,z3,z5,z6]),(0,[z1,z1267,z2,z3,z5,z6])],[(0,[z127,z102,z2,z3,z18,z6]),(0,[z262,z2,z36,z3,z5,z6]),(0,[z0,z1,z2,z51,z104,z6]),(0,[z0,z1,z2,z3,z6,z1268]),(0,[z288,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z266,z411,z6]),(0,[z0,z1,z130,z161,z22,z6])],[(0,[z0,z1,z2,z51,z3,z6]),(0,[z0,z1,z2,z3,z1269,z6]),(0,[z0,z1,z2,z332,z366,z6]),(0,[z1270,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z268,z411,z6])],[(0,[z568,z102,z2,z3,z5,z6]),(0,[z0,z1,z1271,z3,z5,z6]),(0,[z0,z1,z44,z5,z442,z26])],[(0,[z0,z1,z2,z3,z1272,z6]),(0,[z1,z2,z199,z3,z7,z6]),(0,[z0,z498,z2,z51,z3,z6]),(0,[z0,z1,z485,z3,z6,z37])],[(0,[z0,z1,z2,z3,z1273,z6]),(0,[z917,z1,z2,z3,z5,z6]),(0,[z0,z1,z44,z2,z5,z26])],[(0,[z0,z1,z2,z3,z205,z6]),(0,[z594,z1,z153,z3,z5,z6]),(0,[z0,z1274,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1275,z6]),(0,[z0,z1,z2,z3,z1276,z6]),(0,[z488,z1,z2,z3,z893,z6]),(0,[z0,z202,z2,z51,z3,z6])],[(0,[z0,z1,z44,z2,z18,z26]),(0,[z0,z25,z122,z3,z5,z6])],[(0,[z0,z1,z2,z3,z208,z6]),(0,[z0,z1,z550,z3,z22,z6]),(0,[z0,z739,z141,z3,z5,z6]),(0,[z185,z1,z2,z3,z22,z6])],[(0,[z0,z1,z141,z3,z6,z37]),(0,[z0,z1,z2,z1277,z3,z6]),(0,[z70,z0,z2,z3,z5,z31]),(0,[z0,z1,z1078,z3,z5,z6])],[(0,[z0,z1278,z1,z2,z3,z6]),(0,[z0,z1,z2,z1279,z3,z6]),(0,[z0,z1,z2,z3,z6,z780])],[(0,[z0,z1,z2,z3,z1280,z6]),(0,[z0,z369,z1,z2,z374,z6]),(0,[z70,z0,z2,z3,z18,z31]),(0,[z334,z0,z1,z3,z5,z117]),(0,[z70,z488,z2,z3,z5,z31]),(0,[z0,z1,z2,z3,z5,z936]),(0,[z0,z1,z155,z3,z6,z37]),(0,[z0,z1,z2,z1083,z573,z6])],[(0,[z0,z156,z2,z3,z6,z37]),(0,[z1,z153,z3,z5,z6,z228]),(0,[z644,z1,z2,z3,z7,z6]),(0,[z509,z1,z2,z3,z18,z6]),(0,[z0,z1281,z2,z3,z5,z6]),(0,[z56,z0,z1,z3,z599,z117])]],
   [[],[(0,[z0,z1282,z2,z3,z5,z6]),(0,[z0,z1,z1283,z2,z3,z6]),(0,[z0,z1,z1284,z2,z3,z6])],[(0,[z295,z1,z2,z3,z5,z6]),(0,[z90,z24,z1,z2,z177,z6]),(0,[z0,z1,z2,z466,z7,z6]),(0,[z1006,z1,z2,z3,z5,z6]),(0,[z0,z1,z1285,z2,z22,z6])],[(0,[z0,z216,z141,z3,z6,z37]),(0,[z0,z1,z2,z3,z899,z6])],[(0,[z235,z1,z2,z3,z5,z6]),(0,[z295,z1,z2,z3,z18,z6])],[(0,[z0,z1286,z2,z3,z5,z6]),(0,[z0,z1,z1287,z2,z3,z6]),(0,[z0,z1,z505,z3,z5,z6]),(0,[z1288,z1,z2,z3,z5,z6]),(0,[z0,z359,z24,z2,z3,z6]),(0,[z0,z1,z2,z3,z1289,z6])],[(0,[z0,z102,z251,z3,z5,z6]),(0,[z0,z1,z2,z3,z129,z6]),(0,[z0,z1,z2,z3,z1290,z6]),(0,[z90,z1,z2,z177,z281,z6]),(0,[z0,z415,z2,z3,z7,z6]),(0,[z0,z1,z2,z1291,z5,z6]),(0,[z377,z1,z149,z3,z5,z6]),(0,[z0,z1,z3,z5,z6,z442]),(1,[z870,z1,z2,z3,z6])],[(0,[z0,z1,z505,z3,z18,z6]),(0,[z0,z1,z2,z3,z348,z80]),(0,[z0,z1,z2,z1292,z5,z6]),(0,[z0,z1,z505,z3,z6,z905])],[],[(0,[z0,z262,z2,z3,z7,z6]),(0,[z0,z1,z2,z57,z5,z6]),(0,[z1293,z1,z2,z3,z5,z6])],[(0,[z288,z1,z2,z3,z7,z6]),(0,[z0,z1,z130,z161,z7,z6]),(0,[z0,z1,z2,z3,z1294,z6]),(0,[z0,z1,z2,z3,z1295,z6]),(0,[z0,z1,z2,z5,z6,z780])],[(0,[z1,z2,z3,z668,z7,z6]),(0,[z0,z1,z2,z3,z160,z6]),(0,[z0,z1,z2,z1088,z6,z37]),(0,[z0,z1,z3,z22,z6,z361])],[(0,[z81,z1,z2,z51,z36,z6]),(0,[z0,z1,z2,z3,z1296,z6]),(0,[z0,z1,z1297,z2,z3,z6])],[(0,[z0,z1,z1298,z3,z5,z6]),(0,[z0,z1,z2,z3,z1299,z6]),(0,[z0,z1,z3,z5,z6,z1300])],[(0,[z262,z2,z3,z5,z6,z75]),(0,[z0,z230,z25,z3,z5,z6])],[(0,[z0,z23,z2,z627,z5,z6]),(0,[z288,z24,z1,z2,z3,z6]),(0,[z488,z1,z2,z266,z5,z6])]],
   [[(0,[z109,z1,z153,z3,z6,z245]),(0,[z0,z1,z1301,z2,z3,z6]),(0,[z0,z473,z1,z2,z6,z469]),(0,[z0,z1,z2,z1302,z5,z6]),(0,[z0,z1,z55,z2,z51,z6]),(0,[z14,z1,z2,z3,z946,z6]),(0,[z1303,z1,z2,z3,z5,z6])],[(0,[z0,z2,z3,z5,z6,z1304]),(0,[z185,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z844,z6]),(0,[z0,z1,z25,z51,z3,z6])],[(0,[z0,z1,z1305,z2,z3,z6]),(0,[z0,z1,z2,z3,z1306,z6])],[(0,[z0,z1,z1307,z3,z5,z6]),(0,[z0,z415,z283,z3,z5,z6]),(0,[z0,z1,z20,z3,z6,z226]),(0,[z0,z1,z3,z6,z1164,z37]),(0,[z0,z1,z55,z2,z6,z13])],[(0,[z504,z0,z141,z3,z5,z6]),(0,[z109,z125,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1308,z6]),(0,[z0,z1,z2,z3,z1309,z6]),(0,[z0,z1,z3,z5,z1132,z117])],[(0,[z127,z102,z2,z3,z128,z6]),(0,[z0,z1,z1310,z3,z5,z6]),(0,[z0,z1311,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1312,z6]),(0,[z1111,z1,z2,z3,z5,z6]),(0,[z0,z1313,z1,z2,z3,z6])],[(0,[z0,z1,z107,z3,z5,z6]),(0,[z1,z107,z36,z3,z5,z6]),(0,[z638,z0,z141,z3,z5,z6]),(0,[z59,z0,z1,z3,z6,z37]),(0,[z0,z1,z2,z51,z632,z6]),(0,[z185,z24,z1,z2,z3,z6])],[(0,[z356,z1,z2,z3,z18,z6]),(0,[z0,z1,z505,z268,z5,z6])],[(0,[z0,z498,z107,z3,z5,z6]),(0,[z85,z1,z2,z3,z366,z75]),(0,[z70,z0,z25,z3,z5,z31])],[(0,[z0,z1,z2,z3,z1090,z6]),(0,[z0,z1,z149,z3,z22,z6]),(0,[z70,z0,z2,z3,z31,z37]),(0,[z0,z1,z2,z1314,z3,z6]),(0,[z0,z1,z2,z3,z1315,z6])],[(0,[z416,z102,z2,z3,z7,z6]),(0,[z1,z2,z36,z332,z5,z6]),(0,[z0,z1,z3,z294,z6,z37]),(0,[z0,z1,z133,z3,z5,z6])],[(0,[z0,z1,z1316,z3,z5,z6])],[(0,[z0,z1,z133,z3,z18,z6]),(0,[z0,z1,z2,z3,z1317,z6]),(0,[z64,z1,z3,z5,z6,z117])],[(0,[z0,z1,z2,z3,z1318,z6]),(0,[z147,z1,z20,z3,z5,z6])],[(0,[z0,z1,z2,z3,z1319,z6]),(0,[z0,z180,z1,z2,z6,z26]),(0,[z0,z1,z2,z266,z6,z37]),(0,[z0,z1320,z2,z3,z5,z6])],[(0,[z0,z1,z2,z1321,z3,z6]),(0,[z64,z1,z2,z3,z5,z6]),(0,[z0,z1,z467,z3,z22,z6]),(0,[z1,z2,z374,z199,z3,z6]),(0,[z0,z1,z2,z3,z1322,z6]),(0,[z0,z1,z2,z268,z6,z37]),(0,[z0,z1,z2,z573,z22,z6]),(0,[z0,z1,z2,z1323,z22,z6])]],
   [[(0,[z0,z1,z1324,z3,z5,z6]),(0,[z109,z1,z153,z3,z280,z6]),(0,[z0,z1,z2,z1325,z6,z245]),(0,[z235,z1,z25,z3,z5,z6]),(0,[z0,z1,z2,z51,z266,z6]),(0,[z0,z1326,z2,z3,z5,z6]),(0,[z0,z88,z1,z2,z6,z521]),(0,[z0,z1327,z1,z2,z3,z6])],[(0,[z64,z1,z2,z3,z18,z6]),(0,[z0,z1328,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z1329,z6]),(0,[z1,z2,z3,z1330,z6,z111])],[(0,[z1331,z1,z2,z3,z5,z6]),(0,[z0,z1,z326,z3,z6,z37]),(0,[z185,z1,z2,z3,z1332,z6])],[(0,[z0,z10,z2,z3,z190,z6]),(0,[z0,z1,z107,z3,z256,z6])],[(0,[z0,z1,z2,z3,z1333,z6]),(0,[z0,z1,z1063,z2,z5,z6])],[],[(0,[z0,z1,z2,z104,z5,z6]),(0,[z14,z1,z2,z332,z5,z6]),(0,[z0,z1,z25,z3,z160,z6])],[(0,[z109,z306,z153,z3,z5,z6]),(0,[z0,z1,z2,z1334,z3,z6]),(0,[z0,z1,z1335,z2,z3,z6])],[(0,[z0,z1,z2,z3,z6,z1336]),(0,[z0,z1,z2,z104,z18,z6]),(0,[z0,z1,z2,z3,z1337,z6]),(0,[z0,z1,z130,z161,z6,z554]),(0,[z0,z1,z155,z51,z3,z6])],[(0,[z0,z1,z1338,z3,z5,z6]),(0,[z0,z156,z2,z51,z3,z6])],[(0,[z0,z1,z2,z3,z1339,z6]),(0,[z0,z1,z408,z3,z6,z37])],[(0,[z0,z1340,z1,z2,z3,z6]),(0,[z0,z1,z2,z1341,z3,z6]),(0,[z0,z141,z132,z3,z5,z6]),(0,[z0,z24,z1,z2,z6,z521]),(0,[z0,z24,z1,z2,z6,z689])],[(0,[z0,z1,z2,z3,z138,z6]),(0,[z0,z1,z2,z3,z6,z1342]),(0,[z0,z1,z55,z2,z6,z26])],[(0,[z0,z1343,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z818,z75]),(0,[z70,z0,z24,z2,z3,z31]),(0,[z0,z24,z1,z2,z466,z6])],[(0,[z0,z1,z149,z3,z7,z6]),(0,[z0,z1344,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1345,z6]),(0,[z0,z1,z2,z3,z6,z1346]),(0,[z0,z1,z3,z360,z6,z37]),(0,[z426,z0,z1,z539,z3,z6])]],
   [[(0,[z0,z1,z2,z3,z1347,z6]),(0,[z0,z238,z141,z3,z5,z6]),(0,[z377,z1,z2,z3,z29,z6]),(0,[z288,z1,z149,z3,z5,z6]),(0,[z56,z0,z1,z3,z43,z117])],[],[(0,[z0,z415,z467,z3,z5,z6]),(0,[z0,z1,z2,z3,z1348,z6]),(0,[z0,z1,z195,z51,z3,z6])],[(0,[z0,z202,z2,z3,z357,z6])],[],[(0,[z0,z1,z2,z573,z7,z6]),(0,[z0,z1,z2,z3,z1349,z6]),(0,[z0,z10,z2,z3,z493,z6]),(0,[z1,z2,z3,z5,z6,z1350])],[(0,[z398,z1,z2,z3,z7,z6]),(0,[z998,z1,z2,z3,z6,z37])],[(0,[z127,z102,z222,z3,z5,z6]),(0,[z0,z1,z2,z3,z1351,z6]),(0,[z0,z1,z2,z332,z6,z37]),(0,[z0,z1,z2,z1122,z5,z6]),(0,[z0,z1,z2,z3,z1352,z6]),(0,[z0,z1,z2,z3,z1353,z6]),(0,[z1,z2,z3,z22,z6,z111])],[(0,[z0,z1,z2,z3,z1354,z6]),(0,[z0,z1,z2,z3,z1355,z6]),(0,[z0,z1,z2,z3,z1356,z6]),(0,[z0,z284,z2,z3,z54,z6])],[(0,[z0,z1357,z1,z2,z3,z6]),(0,[z87,z1,z2,z3,z7,z6]),(0,[z0,z498,z86,z3,z5,z6]),(0,[z1,z339,z2,z3,z6,z37])],[(0,[z0,z1,z2,z3,z6,z1358]),(0,[z0,z1,z2,z3,z1359,z6]),(0,[z295,z1,z2,z3,z11,z6]),(0,[z1360,z1,z2,z3,z5,z6]),(0,[z0,z1,z1361,z2,z3,z6])],[(0,[z0,z1,z2,z3,z1362,z6]),(0,[z0,z156,z2,z3,z129,z6]),(0,[z90,z1,z2,z177,z22,z6]),(0,[z0,z1,z2,z3,z1167,z6]),(0,[z0,z1363,z1,z2,z3,z6]),(0,[z1364,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1365,z6]),(0,[z0,z1,z2,z3,z1366,z6])],[(0,[z0,z1,z1367,z3,z5,z6]),(0,[z0,z1,z2,z1368,z5,z6])],[(0,[z102,z2,z3,z312,z7,z6]),(0,[z1,z2,z3,z176,z7,z6]),(0,[z185,z1,z2,z573,z5,z6]),(0,[z0,z1,z1369,z2,z3,z6])],[(0,[z0,z1,z2,z3,z207,z6]),(0,[z0,z1370,z2,z3,z5,z6])],[(0,[z0,z1371,z2,z3,z5,z6]),(0,[z0,z1372,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1373,z6])]],
   [[(0,[z125,z1,z102,z2,z3,z6]),(0,[z0,z1,z2,z51,z618,z6]),(0,[z1,z339,z48,z3,z5,z6])],[(0,[z0,z1,z2,z3,z1374,z6]),(0,[z0,z1,z2,z1375,z5,z6])],[(0,[z1,z102,z2,z3,z19,z6]),(0,[z0,z1376,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1377,z6]),(0,[z0,z1,z1378,z3,z5,z6]),(0,[z0,z1,z83,z3,z114,z6])],[(0,[z626,z0,z2,z3,z5,z31]),(0,[z0,z1,z2,z3,z1379,z6]),(0,[z90,z1,z2,z199,z3,z6]),(0,[z0,z1,z2,z3,z1380,z6]),(0,[z0,z1,z2,z3,z1381,z6]),(0,[z0,z1382,z1,z2,z3,z6]),(0,[z0,z1,z44,z2,z37,z26]),(0,[z1383,z24,z1,z2,z3,z6])],[(0,[z1,z1384,z2,z3,z5,z6])],[(0,[z0,z1,z222,z3,z6,z1148]),(0,[z0,z1,z3,z5,z6,z1385]),(0,[z1,z520,z153,z3,z5,z6]),(0,[z0,z1,z2,z3,z6,z226]),(0,[z0,z1386,z2,z3,z5,z6]),(0,[z1,z2,z3,z7,z6,z464]),(0,[z84,z1,z2,z199,z3,z6]),(0,[z0,z1,z2,z3,z1084,z6]),(0,[z1,z2,z3,z471,z18,z6]),(0,[z1131,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z6,z1387]),(0,[z0,z1,z2,z3,z1388,z6]),(0,[z0,z1389,z1,z2,z3,z6]),(0,[z121,z0,z739,z3,z5,z6]),(0,[z0,z24,z1,z2,z6,z780]),(0,[z0,z1,z2,z3,z1390,z6])],[(0,[z0,z1,z2,z3,z1391,z6]),(0,[z0,z494,z2,z3,z6,z37]),(0,[z0,z1,z1123,z3,z5,z6]),(0,[z1133,z1,z2,z3,z5,z6]),(0,[z377,z1,z2,z3,z778,z6]),(0,[z1,z339,z130,z3,z5,z6]),(0,[z0,z2,z3,z22,z6,z100])],[(0,[z0,z1,z1392,z2,z3,z6]),(0,[z1,z213,z2,z3,z7,z6]),(0,[z0,z431,z2,z3,z190,z6]),(0,[z0,z1,z2,z321,z161,z6]),(0,[z439,z1,z2,z3,z208,z6])],[(0,[z0,z1,z2,z1393,z3,z6]),(0,[z0,z1,z2,z3,z944,z6]),(0,[z235,z1,z2,z3,z18,z6]),(0,[z0,z1394,z1,z2,z3,z6]),(0,[z0,z1395,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z1396,z6]),(0,[z0,z1,z2,z3,z1397,z6]),(0,[z0,z1,z3,z5,z6,z1132]),(0,[z0,z1,z2,z3,z1398,z6]),(0,[z0,z1399,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z1400,z6]),(0,[z0,z1,z2,z3,z6,z21]),(0,[z0,z1401,z1,z2,z3,z6]),(0,[z185,z1,z2,z3,z599,z6])],[(0,[z0,z1,z2,z3,z1402,z6]),(0,[z252,z1,z2,z3,z5,z6]),(0,[z0,z369,z1,z2,z3,z6]),(0,[z84,z1,z2,z3,z18,z6]),(0,[z0,z1,z428,z3,z6,z37]),(0,[z0,z1,z2,z3,z5,z1403])],[(0,[z0,z1404,z2,z3,z5,z6]),(0,[z415,z2,z36,z3,z5,z6]),(0,[z0,z498,z2,z3,z22,z6]),(0,[z0,z289,z1,z2,z51,z6])],[(0,[z0,z1405,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1406,z6]),(0,[z0,z1,z2,z57,z18,z6]),(0,[z252,z1,z2,z3,z18,z6]),(0,[z0,z2,z3,z1122,z5,z6]),(0,[z284,z339,z2,z3,z5,z6]),(0,[z46,z0,z322,z2,z3,z6]),(0,[z0,z1,z61,z2,z6,z26])],[(0,[z147,z1,z2,z3,z5,z6]),(0,[z425,z102,z2,z3,z5,z6]),(0,[z0,z202,z2,z3,z22,z6])]],
   [[(0,[z70,z0,z2,z266,z5,z31]),(0,[z0,z1407,z2,z3,z5,z6]),(0,[z14,z24,z1,z2,z6,z26])],[(0,[z90,z1,z2,z177,z7,z6]),(0,[z147,z1,z2,z3,z18,z6]),(0,[z70,z0,z2,z268,z5,z31]),(0,[z0,z1408,z1,z2,z3,z6]),(0,[z368,z473,z1,z2,z3,z6])],[(0,[z0,z1,z222,z3,z6,z37]),(0,[z0,z1,z2,z3,z1409,z6]),(0,[z0,z1,z885,z2,z153,z6]),(0,[z1,z2,z3,z7,z190,z6]),(0,[z0,z24,z1,z2,z6,z146]),(0,[z0,z1,z1410,z2,z3,z6]),(0,[z185,z1,z2,z3,z1411,z6]),(0,[z0,z1,z2,z3,z1412,z6])],[(0,[z0,z141,z122,z3,z6,z37]),(0,[z0,z96,z20,z3,z6,z37]),(0,[z0,z1,z2,z3,z1413,z6]),(0,[z0,z1414,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z1415,z6]),(0,[z0,z1,z2,z3,z1416,z6]),(0,[z0,z141,z3,z6,z31,z37]),(0,[z0,z24,z1,z505,z3,z6]),(0,[z1417,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z1418,z6]),(0,[z0,z1,z1419,z3,z5,z6]),(0,[z0,z1,z2,z3,z1420,z6]),(0,[z0,z24,z1,z25,z3,z6])],[(0,[z0,z1,z2,z3,z1215,z6]),(0,[z0,z1,z1421,z3,z5,z6]),(0,[z0,z1,z2,z3,z6,z1422]),(0,[z1423,z1,z2,z3,z5,z6]),(0,[z1,z1104,z2,z3,z5,z6])],[(0,[z84,z1,z2,z3,z176,z6]),(0,[z0,z1,z130,z258,z161,z6])],[(0,[z0,z1,z2,z3,z6,z1424]),(0,[z663,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z51,z538,z6]),(0,[z235,z1,z2,z266,z5,z6])],[(0,[z252,z1,z2,z3,z176,z6]),(0,[z0,z1,z2,z3,z281,z6]),(0,[z0,z1,z2,z3,z6,z1425]),(0,[z0,z1,z2,z3,z1426,z6]),(0,[z235,z1,z2,z268,z5,z6]),(0,[z0,z1,z505,z266,z5,z6]),(0,[z0,z1,z2,z3,z1427,z6]),(0,[z0,z1,z101,z2,z6,z80])],[(0,[z0,z1,z2,z1428,z3,z6]),(0,[z0,z284,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1429,z6]),(0,[z288,z1,z2,z3,z29,z6]),(0,[z0,z88,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z6,z1430])],[(0,[z0,z1,z2,z3,z1330,z6]),(0,[z0,z1,z107,z3,z18,z6]),(0,[z1431,z1,z2,z3,z5,z6]),(0,[z1432,z1,z2,z3,z5,z6])],[(0,[z0,z284,z2,z3,z18,z6]),(0,[z0,z1,z2,z1433,z5,z6]),(0,[z1434,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z1435,z6]),(0,[z0,z1,z118,z3,z6,z37]),(0,[z0,z1,z2,z573,z43,z6]),(0,[z0,z125,z1,z2,z6,z26]),(0,[z0,z24,z1436,z2,z3,z6])],[(0,[z14,z1,z2,z177,z5,z6]),(0,[z0,z430,z2,z3,z6,z37]),(0,[z0,z359,z2,z3,z6,z37]),(0,[z1,z2,z3,z214,z6,z111])],[(0,[z0,z1,z467,z3,z6,z1437]),(0,[z0,z1,z2,z3,z1438,z6]),(0,[z488,z1,z2,z3,z411,z6]),(0,[z0,z1,z2,z266,z160,z6]),(0,[z0,z1,z1439,z3,z5,z6])]],
   [[(0,[z0,z1,z1440,z3,z5,z6]),(0,[z0,z1,z2,z268,z160,z6]),(0,[z56,z0,z1,z3,z5,z117])],[(0,[z0,z1,z2,z3,z7,z6]),(0,[z0,z262,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1441,z6]),(0,[z0,z24,z2,z6,z100,z26]),(0,[z999,z1,z2,z51,z3,z6])],[(0,[z56,z0,z1,z3,z18,z117])],[(0,[z0,z498,z2,z3,z7,z6]),(0,[z0,z1,z864,z2,z5,z6]),(0,[z0,z1,z2,z3,z1442,z6])],[(0,[z0,z1,z2,z3,z1443,z6]),(0,[z1,z339,z2,z51,z3,z6]),(0,[z0,z605,z2,z60,z3,z6])],[(0,[z0,z24,z1,z251,z3,z6]),(0,[z0,z202,z2,z3,z7,z6]),(0,[z0,z24,z1,z2,z104,z6]),(0,[z0,z1,z1444,z3,z5,z6]),(0,[z0,z430,z48,z3,z5,z6]),(0,[z1,z1445,z2,z3,z5,z6])],[(0,[z0,z24,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1446,z6]),(0,[z0,z1,z1447,z3,z5,z6]),(0,[z0,z1,z2,z3,z736,z6]),(0,[z0,z1,z2,z1448,z3,z6])],[(0,[z0,z306,z2,z3,z6,z37]),(0,[z0,z24,z1,z2,z324,z6]),(0,[z0,z1,z25,z3,z22,z6]),(0,[z0,z1,z2,z3,z1449,z6])],[(0,[z0,z1,z2,z3,z1450,z6]),(0,[z0,z1,z2,z1451,z5,z6]),(0,[z0,z1,z1452,z2,z3,z6]),(0,[z0,z1,z1218,z2,z6,z37]),(0,[z0,z24,z1,z2,z3,z741]),(0,[z0,z1,z61,z34,z2,z6])],[(0,[z0,z1,z283,z3,z93,z6])],[(0,[z0,z1,z885,z2,z5,z6]),(0,[z0,z1,z131,z3,z395,z6]),(0,[z121,z260,z141,z3,z5,z6]),(0,[z0,z1,z2,z3,z1453,z6]),(0,[z0,z1,z2,z3,z1454,z6])],[(0,[z0,z24,z1,z2,z513,z6]),(0,[z0,z369,z148,z1,z2,z6]),(0,[z0,z1,z991,z3,z5,z6]),(0,[z0,z1455,z2,z3,z5,z6])],[(0,[z354,z1,z2,z3,z5,z75]),(0,[z0,z1,z2,z3,z1456,z6]),(0,[z603,z1,z2,z3,z6,z37]),(0,[z0,z1,z3,z22,z6,z442])],[(0,[z0,z1,z2,z1457,z5,z6]),(0,[z0,z1,z2,z3,z6,z1164])],[(0,[z260,z1,z2,z3,z5,z6]),(0,[z239,z102,z2,z3,z5,z6]),(0,[z0,z1,z283,z3,z5,z6]),(0,[z0,z1,z1192,z3,z5,z6]),(0,[z0,z1382,z1,z2,z266,z6]),(0,[z0,z1,z2,z3,z1458,z6]),(0,[z0,z1,z2,z3,z1459,z6]),(0,[z0,z2,z3,z214,z6,z100]),(0,[z0,z1,z1053,z2,z3,z6])],[(0,[z0,z1,z2,z1460,z3,z6]),(0,[z0,z262,z2,z3,z256,z6]),(0,[z0,z1,z2,z573,z599,z6]),(0,[z0,z1,z2,z3,z1461,z6])]],
   [[(0,[z119,z1,z153,z3,z5,z6]),(0,[z0,z1,z283,z3,z18,z6]),(0,[z0,z1462,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1463,z6]),(0,[z260,z1,z2,z3,z18,z6]),(0,[z0,z1,z2,z104,z366,z6]),(0,[z0,z1,z2,z3,z1200,z6]),(0,[z0,z1,z1285,z2,z5,z6]),(0,[z64,z430,z2,z3,z5,z6]),(0,[z24,z1,z2,z3,z6,z111])],[(0,[z1,z306,z153,z3,z5,z6]),(0,[z0,z1,z528,z3,z6,z37]),(0,[z0,z1,z771,z3,z5,z6]),(0,[z0,z23,z2,z1122,z5,z6])],[(0,[z90,z1,z2,z332,z5,z6]),(0,[z0,z494,z2,z51,z3,z6]),(0,[z0,z1,z2,z3,z1464,z6]),(0,[z0,z1,z2,z51,z332,z6]),(0,[z0,z1,z1465,z2,z3,z6]),(0,[z0,z1,z2,z3,z357,z6])],[(0,[z1466,z1,z2,z3,z5,z6])],[(0,[z0,z1,z1467,z2,z5,z6]),(0,[z0,z1,z2,z1468,z5,z6]),(0,[z85,z1,z2,z104,z5,z75]),(0,[z0,z1,z1469,z3,z5,z6])],[(0,[z0,z1,z2,z1470,z3,z6]),(0,[z0,z1,z2,z3,z6,z1471]),(0,[z0,z1,z363,z2,z3,z6]),(0,[z377,z1,z195,z3,z5,z6]),(0,[z0,z1,z591,z2,z51,z6])],[(0,[z0,z1,z537,z3,z6,z37])],[(0,[z0,z1,z251,z3,z461,z6]),(0,[z0,z1,z2,z1472,z5,z6]),(0,[z0,z1,z2,z3,z6,z1473]),(0,[z0,z1,z141,z3,z6,z226])],[(0,[z137,z125,z1,z2,z3,z6]),(0,[z1,z2,z3,z580,z18,z6]),(0,[z0,z1,z2,z3,z1474,z6]),(0,[z121,z0,z141,z3,z5,z6])],[(0,[z1,z2,z3,z853,z7,z6]),(0,[z0,z23,z141,z3,z6,z37]),(0,[z1,z1475,z2,z3,z5,z6]),(0,[z0,z238,z2,z3,z11,z6])],[(0,[z0,z1,z86,z3,z5,z6]),(0,[z121,z0,z141,z3,z18,z6]),(0,[z0,z1,z1476,z2,z3,z6]),(0,[z0,z24,z1,z149,z3,z6]),(0,[z0,z1,z2,z3,z1477,z6])],[(0,[z377,z1,z2,z3,z5,z6]),(0,[z0,z180,z1,z34,z2,z6]),(0,[z0,z1,z2,z3,z6,z1478])],[(0,[z0,z72,z24,z1,z2,z6]),(0,[z0,z1,z2,z1479,z5,z6]),(0,[z0,z1,z86,z3,z18,z6]),(0,[z185,z1,z2,z3,z43,z6]),(0,[z0,z1,z2,z6,z1430,z26]),(0,[z1168,z1,z2,z51,z3,z6])],[(0,[z0,z1,z222,z51,z3,z6]),(0,[z127,z102,z2,z3,z6,z37]),(0,[z90,z125,z1,z2,z3,z6]),(0,[z0,z1,z25,z3,z7,z6]),(0,[z377,z1,z2,z3,z18,z6]),(0,[z1480,z1,z2,z3,z5,z6]),(0,[z1481,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z1482,z3,z6]),(0,[z0,z1,z2,z3,z246,z80])],[(0,[z0,z1,z2,z5,z1325,z6])],[(0,[z0,z1,z2,z3,z1483,z6]),(0,[z1,z467,z36,z3,z5,z6]),(0,[z377,z1,z2,z3,z745,z6]),(0,[z0,z1,z149,z3,z29,z6]),(0,[z0,z1484,z2,z3,z5,z6]),(0,[z0,z1,z155,z3,z22,z6])]],
   [[(0,[z306,z2,z153,z3,z5,z6]),(0,[z0,z156,z2,z3,z22,z6]),(0,[z0,z1,z2,z374,z3,z6]),(0,[z1485,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1486,z6]),(0,[z0,z1,z195,z3,z1381,z6]),(0,[z0,z1,z2,z3,z6,z554]),(0,[z0,z1,z719,z130,z5,z6]),(0,[z0,z1,z1487,z2,z3,z6])],[(0,[z0,z1488,z2,z3,z5,z6]),(0,[z147,z1,z141,z3,z5,z6]),(0,[z235,z23,z2,z3,z5,z6]),(0,[z1489,z1,z2,z3,z5,z6]),(0,[z0,z1,z101,z2,z6,z37]),(0,[z0,z1,z539,z3,z22,z6]),(0,[z56,z64,z1,z3,z5,z117]),(0,[z0,z24,z1,z2,z300,z6]),(0,[z0,z1,z2,z3,z556,z6]),(0,[z14,z1,z3,z5,z6,z442])],[(0,[z0,z1,z251,z3,z5,z6]),(0,[z0,z1,z2,z7,z1325,z6]),(0,[z0,z1,z2,z3,z1490,z6]),(0,[z0,z24,z1,z2,z529,z6]),(0,[z0,z1,z2,z3,z1491,z6])],[(0,[z1,z102,z2,z3,z281,z6]),(0,[z0,z1,z107,z332,z5,z6]),(0,[z260,z1,z2,z3,z949,z6])],[(0,[z0,z1,z251,z3,z18,z6]),(0,[z0,z1,z2,z3,z1492,z6]),(0,[z0,z1,z2,z365,z3,z6]),(0,[z0,z1,z2,z3,z990,z6]),(0,[z0,z1,z2,z3,z1493,z6]),(0,[z295,z1,z2,z3,z79,z6])],[(0,[z230,z102,z2,z3,z7,z6]),(0,[z137,z1,z2,z3,z6,z245]),(0,[z85,z1,z2,z51,z3,z75])],[(0,[z0,z1,z2,z1494,z3,z6]),(0,[z0,z1,z2,z3,z1495,z6]),(0,[z181,z1,z2,z3,z140,z6]),(0,[z0,z1,z2,z3,z994,z6]),(0,[z0,z1,z2,z1496,z3,z6])],[(0,[z0,z1011,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1497,z6]),(0,[z0,z24,z1,z145,z2,z6]),(0,[z0,z1,z149,z3,z5,z6])],[(0,[z0,z1,z467,z3,z93,z6]),(0,[z81,z1,z2,z3,z140,z6]),(0,[z0,z1,z86,z3,z256,z6]),(0,[z0,z1498,z1,z2,z104,z6]),(0,[z0,z24,z1,z567,z2,z6]),(0,[z0,z1,z195,z3,z22,z6]),(0,[z0,z429,z1,z2,z3,z6]),(0,[z0,z870,z1,z2,z3,z6]),(0,[z14,z1,z2,z3,z6,z37])],[(0,[z0,z216,z251,z3,z5,z6]),(0,[z91,z0,z1,z539,z3,z6]),(0,[z1499,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z79,z460]),(0,[z488,z1,z2,z3,z6,z37]),(0,[z0,z430,z2,z51,z3,z6]),(0,[z0,z1,z2,z3,z1500,z6])],[(0,[z1,z2,z3,z1180,z5,z6]),(0,[z0,z1,z1501,z2,z3,z6]),(0,[z0,z1502,z2,z3,z5,z6]),(0,[z0,z1,z55,z34,z2,z6]),(0,[z0,z24,z1,z34,z2,z26])],[(0,[z0,z1,z1503,z3,z5,z6]),(0,[z0,z1,z86,z3,z6,z941]),(0,[z0,z1,z20,z3,z6,z143]),(0,[z0,z1,z2,z51,z268,z6]),(0,[z0,z1,z2,z828,z3,z6])],[(0,[z0,z1,z2,z3,z1504,z6]),(0,[z0,z359,z44,z2,z5,z26])],[(0,[z0,z1,z467,z3,z5,z6]),(0,[z0,z1,z2,z3,z1505,z6]),(0,[z125,z1,z2,z3,z6,z75]),(0,[z0,z1,z2,z573,z5,z6])],[(0,[z0,z1,z2,z3,z22,z6]),(0,[z90,z180,z1,z2,z177,z6]),(0,[z279,z1,z2,z3,z7,z6]),(0,[z76,z1,z107,z3,z5,z6]),(0,[z0,z148,z1,z55,z2,z6]),(0,[z56,z0,z1,z3,z5,z197]),(0,[z1219,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z51,z57,z6])],[(0,[z399,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z1506,z5,z6]),(0,[z0,z1507,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1508,z6]),(0,[z0,z1,z2,z3,z1509,z6]),(0,[z235,z1,z2,z3,z1051,z6])]],
   [[(0,[z0,z1,z2,z3,z6,z1510]),(0,[z0,z1,z48,z3,z66,z6])],[(0,[z0,z1,z2,z1511,z3,z6]),(0,[z0,z1512,z1,z2,z3,z6]),(0,[z0,z1,z20,z3,z6,z554]),(0,[z0,z23,z24,z2,z165,z6]),(0,[z0,z24,z1,z2,z266,z6]),(0,[z14,z359,z2,z3,z5,z6])],[(0,[z0,z306,z2,z51,z3,z6]),(0,[z0,z1,z2,z3,z1513,z6]),(0,[z85,z1,z2,z3,z5,z341]),(0,[z0,z1,z1514,z3,z5,z6])],[(0,[z0,z1,z195,z3,z6,z1422]),(0,[z0,z1,z3,z214,z6,z442])],[(0,[z626,z1,z2,z3,z5,z75]),(0,[z0,z1,z2,z3,z1515,z6])],[(0,[z0,z1,z2,z3,z6,z1207]),(0,[z0,z1,z2,z3,z1516,z6]),(0,[z0,z1,z1517,z3,z5,z6]),(0,[z0,z1,z155,z3,z7,z6]),(0,[z0,z2,z122,z268,z5,z6]),(0,[z0,z1,z133,z3,z11,z6]),(0,[z0,z1,z1518,z2,z3,z6])],[(0,[z0,z156,z2,z3,z7,z6]),(0,[z0,z1,z2,z445,z3,z6]),(0,[z0,z1,z2,z3,z1519,z6]),(0,[z0,z1,z2,z3,z1520,z6])],[(0,[z0,z1,z1521,z3,z5,z6]),(0,[z1,z2,z3,z7,z6,z630]),(0,[z603,z1,z2,z51,z3,z6]),(0,[z0,z1,z2,z3,z98,z80])],[(0,[z0,z1,z2,z3,z6,z1522]),(0,[z0,z1,z2,z3,z1523,z6])],[(0,[z0,z1,z2,z1524,z3,z6]),(0,[z0,z1,z454,z3,z6,z37]),(0,[z1,z642,z2,z3,z18,z6]),(0,[z0,z1,z1525,z2,z3,z6]),(0,[z0,z1,z2,z3,z98,z514]),(0,[z0,z24,z1,z155,z6,z26])],[(0,[z175,z1,z2,z3,z7,z6]),(0,[z0,z359,z3,z5,z6,z442])],[(0,[z0,z1,z2,z3,z1101,z6]),(0,[z0,z24,z1,z2,z6,z373])],[(0,[z109,z1,z153,z3,z6,z37]),(0,[z0,z369,z1,z2,z177,z6]),(0,[z0,z415,z2,z3,z93,z6]),(1,[z0,z1,z817,z3,z6]),(0,[z181,z125,z1,z2,z3,z6]),(0,[z0,z1,z133,z3,z79,z6])],[(0,[z0,z1526,z2,z3,z5,z6]),(0,[z0,z1,z1527,z3,z5,z6]),(0,[z1528,z1,z2,z3,z5,z6]),(0,[z0,z1,z508,z3,z66,z6]),(0,[z0,z1,z2,z1529,z5,z6]),(0,[z0,z430,z2,z57,z5,z6]),(0,[z56,z0,z24,z1,z3,z117]),(0,[z0,z1,z2,z1530,z3,z6]),(0,[z0,z1,z2,z466,z5,z6])],[(0,[z137,z1,z2,z3,z272,z6]),(0,[z0,z1,z195,z3,z7,z6]),(0,[z1,z339,z2,z3,z357,z6])],[(0,[z0,z1531,z2,z3,z5,z6]),(0,[z0,z369,z1,z2,z6,z455]),(0,[z0,z1,z2,z892,z7,z6]),(0,[z0,z1,z2,z466,z18,z6]),(0,[z288,z1,z195,z3,z5,z6]),(0,[z0,z605,z2,z3,z11,z6]),(0,[z0,z1,z2,z266,z22,z6]),(0,[z0,z24,z1,z607,z2,z6]),(0,[z14,z2,z3,z5,z6,z100])]],
   [[(0,[z1532,z1,z2,z3,z5,z6]),(0,[z0,z24,z1,z195,z3,z6]),(0,[z0,z1,z25,z3,z6,z1533]),(0,[z0,z1,z2,z268,z22,z6]),(0,[z70,z0,z2,z3,z411,z31]),(0,[z0,z1,z499,z3,z6,z37]),(0,[z0,z1,z2,z51,z573,z6]),(0,[z1534,z1,z2,z3,z5,z6])],[(0,[z0,z415,z2,z3,z5,z6]),(0,[z0,z1,z2,z1535,z5,z6]),(0,[z0,z1,z2,z3,z1536,z6]),(0,[z0,z1,z2,z1537,z3,z6]),(0,[z0,z1,z2,z3,z1538,z6]),(0,[z0,z1,z1539,z2,z3,z6])],[(0,[z0,z1,z2,z1540,z5,z6]),(0,[z0,z1,z107,z3,z366,z6]),(0,[z0,z23,z2,z165,z22,z6]),(0,[z235,z2,z3,z5,z6,z31]),(0,[z0,z1,z2,z3,z1411,z6]),(0,[z0,z1,z155,z3,z518,z6])],[(0,[z0,z306,z2,z3,z129,z6]),(0,[z510,z0,z141,z3,z5,z6]),(0,[z0,z415,z2,z3,z18,z6]),(0,[z0,z1,z1541,z3,z5,z6]),(0,[z0,z635,z2,z3,z11,z6]),(0,[z0,z24,z284,z2,z3,z6]),(0,[z1542,z1,z2,z3,z5,z6]),(0,[z0,z24,z1,z2,z6,z1430])],[(0,[z0,z1,z2,z3,z851,z6]),(0,[z0,z1,z2,z1543,z5,z6]),(0,[z0,z1,z86,z332,z5,z6]),(0,[z0,z1,z2,z3,z6,z1544]),(0,[z295,z1,z83,z3,z5,z6])],[(0,[z288,z1,z2,z3,z5,z6]),(0,[z137,z1,z2,z3,z140,z6]),(0,[z0,z1545,z1,z2,z3,z6]),(0,[z1546,z1,z2,z3,z5,z6]),(0,[z0,z1,z130,z161,z5,z6])],[(0,[z0,z1,z2,z3,z853,z6]),(0,[z0,z262,z2,z3,z18,z6]),(0,[z85,z1,z107,z3,z5,z75]),(0,[z0,z1,z2,z1547,z104,z6])],[(0,[z288,z1,z2,z3,z18,z6]),(0,[z0,z1,z130,z161,z18,z6]),(0,[z0,z1,z2,z1547,z3,z6]),(0,[z0,z1,z2,z3,z1548,z6]),(0,[z24,z295,z1,z2,z3,z6])],[(0,[z127,z102,z2,z51,z3,z6]),(0,[z0,z1,z2,z3,z1549,z6]),(0,[z0,z1,z2,z1550,z3,z6]),(0,[z235,z1,z2,z3,z411,z6])],[(0,[z137,z1,z2,z3,z128,z6]),(0,[z0,z1,z2,z3,z1551,z6]),(0,[z0,z1,z505,z3,z411,z6]),(0,[z0,z2,z3,z5,z6,z1552]),(0,[z0,z1,z3,z22,z6,z275])],[(0,[z0,z1,z2,z1553,z5,z6])],[(0,[z0,z1,z1554,z3,z5,z6]),(0,[z0,z1,z2,z1555,z3,z6]),(0,[z1556,z1,z2,z3,z5,z6]),(0,[z56,z0,z1,z3,z37,z117])],[(0,[z0,z1,z2,z3,z4,z6]),(0,[z185,z1,z2,z3,z5,z6]),(0,[z0,z1,z885,z2,z6,z245]),(0,[z0,z1,z2,z1325,z6,z37])],[(0,[z85,z1,z2,z3,z75,z37])],[(0,[z418,z1,z153,z3,z5,z6]),(0,[z0,z1,z2,z3,z6,z1557]),(0,[z185,z1,z2,z3,z18,z6])],[(0,[z0,z1,z932,z3,z5,z6]),(0,[z0,z1,z2,z1558,z5,z6]),(0,[z1,z2,z3,z7,z6,z247]),(0,[z0,z1,z1559,z3,z5,z6]),(0,[z0,z1,z83,z3,z6,z37]),(0,[z0,z1,z2,z3,z30,z6]),(0,[z0,z430,z130,z3,z5,z6])]],
   [[(0,[z0,z1560,z2,z3,z5,z6]),(0,[z0,z24,z1,z2,z424,z6]),(0,[z0,z918,z1,z2,z3,z6]),(0,[z0,z1,z1561,z3,z5,z6])],[(0,[z0,z1,z2,z3,z29,z6]),(0,[z0,z24,z1,z2,z480,z6]),(0,[z0,z1,z2,z3,z1562,z6]),(0,[z0,z1,z2,z3,z518,z6]),(0,[z0,z1,z485,z508,z3,z6])],[(0,[z0,z1,z2,z104,z6,z37]),(0,[z0,z1,z141,z3,z6,z554]),(0,[z0,z1,z2,z3,z1563,z6]),(0,[z0,z1,z2,z1314,z57,z6])],[(0,[z1,z2,z1180,z177,z5,z6]),(0,[z0,z1,z283,z3,z1042,z6]),(0,[z0,z1,z1015,z3,z5,z6]),(0,[z14,z1,z2,z51,z3,z6])],[(0,[z0,z1,z2,z3,z1564,z6]),(0,[z488,z1,z2,z51,z3,z6])],[(0,[z416,z102,z2,z3,z5,z6]),(0,[z0,z1,z2,z266,z7,z6]),(0,[z0,z1,z2,z1565,z3,z6])],[(0,[z0,z1,z2,z3,z6,z1566]),(0,[z137,z1,z2,z3,z1134,z6]),(0,[z0,z943,z1,z2,z7,z6]),(0,[z0,z1,z2,z268,z7,z6]),(0,[z0,z1,z2,z3,z1567,z6]),(0,[z0,z1,z2,z3,z1568,z6]),(0,[z0,z1,z2,z3,z6,z1569]),(0,[z0,z1,z2,z3,z1332,z6]),(0,[z0,z1,z71,z539,z3,z6]),(0,[z14,z1,z44,z2,z5,z26])],[(0,[z0,z1,z2,z3,z6,z1570]),(0,[z1571,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z18,z7,z6]),(0,[z0,z23,z2,z165,z7,z6]),(0,[z0,z1,z2,z332,z22,z6])],[(0,[z0,z1572,z2,z3,z5,z6]),(0,[z0,z1,z283,z3,z344,z6]),(0,[z0,z1,z2,z3,z1573,z6]),(0,[z0,z10,z83,z3,z11,z6]),(0,[z59,z0,z1,z3,z6,z1164])],[(0,[z0,z1,z2,z1574,z3,z6]),(0,[z1,z2,z3,z18,z853,z6]),(0,[z0,z1,z154,z2,z3,z6]),(0,[z0,z24,z1,z2,z6,z447]),(0,[z1,z339,z2,z3,z22,z6]),(0,[z0,z1575,z2,z3,z5,z6]),(0,[z0,z125,z1,z34,z2,z6])],[(0,[z0,z1,z2,z3,z1576,z6]),(0,[z0,z1,z2,z1577,z5,z6]),(0,[z0,z1,z2,z3,z6,z1578])],[(0,[z0,z24,z494,z2,z3,z6]),(0,[z0,z1,z283,z3,z6,z922]),(0,[z0,z473,z1,z2,z445,z6]),(0,[z1,z1579,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1580,z6]),(0,[z0,z1,z1581,z2,z3,z6]),(0,[z0,z1,z1582,z2,z3,z6])],[(0,[z0,z1,z2,z1583,z5,z6]),(0,[z0,z166,z2,z3,z6,z37]),(0,[z0,z1,z2,z3,z6,z143])],[(0,[z0,z1,z3,z22,z6,z106]),(0,[z0,z1,z2,z3,z152,z6]),(0,[z0,z1,z135,z2,z3,z246]),(0,[z0,z1,z155,z3,z214,z6]),(0,[z0,z1,z1053,z2,z3,z5])],[(0,[z0,z1,z2,z3,z1584,z6]),(0,[z0,z1,z1585,z2,z3,z6])]],
   [[(0,[z1586,z1,z2,z3,z5,z6]),(0,[z1587,z1,z2,z3,z5,z6])],[(0,[z0,z1588,z1,z2,z3,z6]),(0,[z0,z1,z1589,z3,z5,z6]),(0,[z0,z1,z2,z1590,z5,z6]),(0,[z0,z1,z130,z161,z286,z6]),(0,[z0,z1,z155,z573,z5,z6]),(0,[z0,z1,z1591,z2,z3,z6]),(0,[z0,z24,z1,z44,z2,z26]),(0,[z0,z1,z1592,z3,z5,z6])],[(0,[z0,z24,z1,z2,z6,z469]),(0,[z0,z1593,z2,z3,z5,z6]),(0,[z0,z10,z1,z101,z2,z6]),(0,[z0,z1,z3,z6,z442,z37])],[(0,[z87,z1,z153,z3,z5,z6]),(0,[z0,z1594,z2,z3,z5,z6]),(0,[z0,z1,z1595,z3,z5,z6]),(0,[z0,z1,z1589,z3,z18,z6]),(0,[z0,z387,z1,z3,z6,z37]),(0,[z0,z1,z20,z539,z3,z6]),(0,[z1596,z1,z2,z3,z5,z6]),(0,[z14,z1,z2,z3,z1289,z6])],[(0,[z158,z0,z1,z3,z6,z113]),(0,[z0,z24,z1,z182,z2,z6]),(0,[z0,z1,z2,z3,z1597,z6]),(0,[z334,z0,z2,z3,z5,z31]),(0,[z488,z1,z505,z3,z5,z6]),(0,[z0,z956,z2,z3,z5,z6])],[(0,[z70,z235,z2,z3,z5,z31])],[(0,[z1,z2,z3,z208,z140,z6]),(0,[z0,z1598,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1599,z6]),(0,[z413,z1,z2,z3,z18,z6])],[(0,[z0,z1,z1600,z2,z3,z6]),(0,[z109,z1,z153,z51,z3,z6]),(0,[z0,z1,z1601,z3,z5,z6]),(0,[z330,z1,z2,z3,z18,z6]),(0,[z85,z1,z86,z3,z5,z75]),(0,[z0,z1,z2,z3,z6,z1533]),(0,[z0,z1,z2,z3,z1602,z6]),(0,[z0,z1,z719,z2,z5,z6])],[(0,[z147,z1,z2,z3,z273,z6]),(0,[z0,z1,z2,z3,z1603,z6]),(0,[z0,z1,z414,z3,z22,z6])],[(0,[z260,z1,z2,z3,z954,z6]),(0,[z0,z1,z539,z141,z3,z6]),(0,[z0,z1,z155,z3,z1604,z6])],[(0,[z102,z153,z141,z3,z5,z6]),(0,[z0,z1,z2,z1605,z3,z6]),(0,[z0,z1606,z2,z3,z5,z6]),(0,[z0,z331,z141,z3,z5,z6]),(0,[z488,z1,z2,z3,z160,z6]),(0,[z0,z24,z1,z130,z161,z6]),(0,[z1,z2,z3,z5,z6,z1607])],[],[(0,[z0,z1,z149,z3,z18,z6]),(0,[z0,z1498,z1,z2,z3,z6]),(0,[z0,z1,z2,z1608,z3,z6]),(0,[z0,z1,z2,z3,z43,z6]),(0,[z0,z359,z2,z51,z3,z6])],[(0,[z109,z1,z153,z3,z208,z6]),(0,[z0,z1,z1609,z2,z3,z6]),(0,[z0,z1,z2,z3,z1610,z6]),(0,[z0,z1,z2,z3,z1611,z6]),(0,[z0,z1,z1612,z2,z3,z6]),(0,[z0,z1,z2,z3,z214,z6])],[(0,[z1,z102,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z1613,z6]),(0,[z0,z1,z2,z3,z6,z1437]),(0,[z0,z1,z2,z3,z6,z1614]),(0,[z0,z1,z2,z332,z7,z6]),(0,[z0,z1,z2,z3,z6,z1615]),(0,[z0,z262,z2,z332,z5,z6]),(0,[z0,z1,z2,z3,z1616,z6])],[(0,[z0,z1617,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1618,z6])]],
   [[(0,[z1,z339,z2,z3,z7,z6]),(0,[z295,z1,z2,z3,z6,z37]),(0,[z0,z1,z1619,z3,z5,z6]),(0,[z0,z1,z2,z1323,z5,z6])],[(0,[z125,z1,z2,z3,z18,z6]),(0,[z0,z1363,z1,z2,z268,z6]),(0,[z0,z1,z2,z3,z1620,z6]),(0,[z0,z1,z2,z5,z6,z964])],[(0,[z0,z1,z467,z3,z18,z6]),(0,[z0,z1,z2,z573,z18,z6]),(0,[z0,z1,z2,z3,z1621,z6]),(0,[z235,z1,z2,z3,z6,z37]),(0,[z0,z1,z585,z3,z6,z37])],[(0,[z0,z1622,z2,z3,z5,z6]),(0,[z0,z1,z505,z3,z6,z37]),(0,[z0,z1,z3,z6,z301,z37]),(0,[z0,z1,z2,z3,z1623,z6])],[(0,[z0,z1,z2,z1624,z5,z6])],[(0,[z1625,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z1626,z3,z6]),(0,[z0,z1,z2,z1627,z3,z6]),(0,[z0,z1,z2,z3,z1628,z6])],[(0,[z0,z1,z2,z3,z1629,z6]),(0,[z0,z1,z2,z3,z1630,z6]),(0,[z90,z1,z2,z1180,z5,z6]),(0,[z0,z1,z2,z3,z1631,z6]),(0,[z0,z1,z1632,z3,z5,z6])],[(0,[z0,z1,z2,z3,z6,z1633]),(0,[z1634,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z57,z6,z37])],[(0,[z109,z1,z153,z3,z129,z6]),(0,[z0,z1,z153,z3,z395,z6]),(0,[z0,z1,z467,z3,z344,z6]),(0,[z0,z1,z817,z3,z5,z6]),(0,[z0,z1,z2,z3,z1635,z6]),(0,[z0,z24,z1,z2,z565,z6]),(0,[z0,z1,z2,z3,z1604,z6])],[(0,[z305,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z1636,z6]),(0,[z62,z1,z2,z3,z7,z6]),(0,[z76,z262,z2,z3,z5,z6]),(0,[z603,z1,z2,z3,z1353,z6]),(0,[z0,z1,z1637,z2,z3,z6]),(0,[z1383,z1,z2,z3,z5,z6]),(0,[z0,z1436,z2,z3,z5,z6])],[(0,[z0,z1638,z1,z2,z3,z6]),(0,[z0,z1639,z2,z3,z5,z6]),(0,[z0,z1,z817,z3,z18,z6]),(0,[z0,z1,z83,z51,z3,z6]),(0,[z343,z0,z1,z3,z6,z37]),(0,[z0,z1,z130,z3,z66,z6]),(0,[z0,z1,z2,z3,z1640,z6])],[(0,[z0,z24,z415,z2,z3,z6]),(0,[z0,z1,z2,z51,z703,z6]),(0,[z85,z1,z2,z3,z22,z75]),(0,[z0,z1,z1641,z2,z3,z6]),(0,[z0,z1642,z2,z3,z5,z6]),(0,[z0,z1,z3,z66,z6,z37])],[(0,[z0,z1,z130,z28,z5,z6])],[(0,[z295,z1,z133,z3,z5,z6])],[(0,[z0,z1643,z1,z2,z3,z6]),(0,[z504,z1,z153,z3,z5,z6]),(0,[z0,z494,z2,z3,z7,z6]),(0,[z0,z1,z73,z3,z6,z37]),(0,[z0,z202,z2,z3,z54,z6]),(0,[z0,z1,z2,z3,z599,z6]),(0,[z0,z1,z2,z3,z1644,z6])],[(0,[z0,z1,z1645,z3,z5,z6]),(0,[z584,z1,z2,z3,z7,z6]),(0,[z0,z1,z130,z45,z5,z6]),(0,[z0,z1,z1646,z3,z5,z6]),(0,[z0,z430,z2,z3,z22,z6])]],
   [[(0,[z0,z24,z1,z283,z3,z6]),(0,[z0,z473,z1,z2,z6,z26]),(0,[z0,z1,z2,z3,z1647,z6]),(0,[z0,z1,z2,z3,z1648,z6]),(0,[z1649,z1,z2,z3,z5,z6]),(0,[z56,z185,z1,z3,z5,z117]),(0,[z215,z1,z2,z199,z3,z6])],[(0,[z252,z10,z2,z3,z11,z6]),(0,[z0,z1,z2,z3,z1040,z6])],[(0,[z0,z1,z2,z3,z1650,z6]),(0,[z0,z473,z1,z817,z3,z6]),(0,[z85,z1,z2,z3,z5,z818]),(0,[z0,z141,z3,z5,z6,z604]),(0,[z0,z1,z2,z3,z1651,z6])],[(0,[z0,z24,z1,z2,z332,z6]),(0,[z0,z1,z149,z3,z6,z796]),(0,[z0,z1,z2,z3,z1097,z6]),(0,[z0,z1,z1652,z3,z5,z6])],[(0,[z0,z1,z2,z3,z1653,z6]),(0,[z0,z1654,z2,z3,z5,z6]),(0,[z0,z1,z107,z3,z6,z37])],[(0,[z0,z1655,z1,z2,z3,z6]),(0,[z0,z1,z2,z1656,z3,z6]),(0,[z0,z1,z2,z3,z1657,z6]),(0,[z0,z1,z2,z3,z1658,z6]),(0,[z0,z1,z670,z2,z51,z6])],[(0,[z0,z1,z2,z3,z1659,z6]),(0,[z1,z2,z3,z6,z226,z245]),(0,[z0,z1,z2,z445,z177,z6]),(0,[z0,z1,z2,z3,z1660,z6]),(0,[z0,z23,z2,z265,z165,z6]),(0,[z0,z1,z2,z3,z1661,z6])],[(0,[z0,z1,z2,z1662,z5,z6]),(0,[z0,z1,z2,z3,z1663,z6]),(0,[z260,z1,z2,z3,z273,z6])],[(0,[z0,z1,z251,z3,z128,z6]),(0,[z0,z306,z2,z3,z22,z6]),(0,[z0,z1,z133,z3,z6,z37]),(0,[z0,z166,z2,z51,z3,z6])],[(0,[z0,z1,z222,z3,z7,z6]),(0,[z0,z1,z2,z3,z395,z6]),(0,[z364,z1,z2,z3,z7,z6]),(0,[z1664,z1,z2,z3,z5,z6])],[(0,[z0,z1,z1665,z2,z3,z6]),(0,[z0,z1,z2,z3,z872,z6]),(0,[z0,z1,z2,z3,z1666,z6])],[(0,[z0,z494,z283,z3,z5,z6]),(0,[z88,z870,z1,z2,z3,z6]),(0,[z0,z24,z1,z34,z2,z250])],[(0,[z90,z1,z2,z177,z5,z6]),(0,[z0,z415,z2,z3,z344,z6]),(0,[z0,z1,z107,z3,z6,z1190]),(0,[z0,z429,z1,z130,z161,z6])],[(0,[z1,z102,z2,z374,z3,z6]),(0,[z96,z102,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z1667,z6]),(0,[z0,z262,z2,z3,z366,z6]),(0,[z0,z1,z48,z155,z5,z6]),(0,[z64,z1,z2,z3,z6,z37])],[(0,[z0,z24,z156,z2,z3,z6]),(0,[z90,z1,z2,z177,z18,z6]),(0,[z0,z1,z2,z3,z6,z1668]),(0,[z0,z1,z195,z3,z29,z6]),(0,[z252,z1,z83,z3,z5,z6]),(0,[z1147,z1,z2,z3,z5,z6]),(0,[z0,z359,z24,z2,z6,z26]),(0,[z0,z1,z1245,z3,z5,z6])],[(0,[z1,z102,z251,z3,z5,z6]),(0,[z0,z1,z2,z3,z1669,z6]),(0,[z1,z613,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z1670,z6]),(0,[z0,z1,z141,z3,z6,z143]),(0,[z0,z24,z1,z985,z3,z6])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 16 512 bkB c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 460) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 460).take 460) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 920).take 460) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1380).take 236) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1616)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [460, 460, 460, 236] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_nil pbend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 104).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 104).take 117).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 221).take 128).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 349).take 117).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 466).take 46).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [104, 117, 128, 117, 46] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_nil pcend)))))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 16) (nb2 := 512) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_36723

theorem PEqualNP.Outside.L_meta_36723 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 4008372896) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372968 * 2 ^ 32 + 4008372896) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_36723.solve