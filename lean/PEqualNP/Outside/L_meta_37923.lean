import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_37923

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
  Nat.testBit (4277074666 * 2 ^ 32 + 4276812448) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x01000000a00282ac#64 ++ 0x0020000014005055#64 ++ 0xfec14463e08f87ff#64 ++ 0xbfd8288c7c11f0ff#64 : BitVec 256),
   (0x02221a4d83366666#64 ++ 0x20444349b066cccc#64 ++ 0xbda6ba5d87766667#64 ++ 0x77b4d74bb0eecccc#64 : BitVec 256),
   (0xa408c09608582850#64 ++ 0x94811812c10b050a#64 ++ 0xebf8c39e1878787e#64 ++ 0xfd7f1873c30f0f0f#64 : BitVec 256),
   (0x0817036015805500#64 ++ 0x2102e06c02b00aa0#64 ++ 0x67df03e01f807f85#64 ++ 0xecfbe07c03f00ff0#64 : BitVec 256),
   (0x301dec001eed0000#64 ++ 0xc603bd8003dda000#64 ++ 0x1fbffc001fff8003#64 ++ 0xe3f7ff8003fff000#64 : BitVec 256),
   (0xc01ff7fb40000000#64 ++ 0xf803feff68000000#64 ++ 0xff9fffffe0000000#64 ++ 0x1ff3fffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 3]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [4, 8]⟩, ⟨.or, [2, 9]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [0, 11]⟩, ⟨.or, [4, 8]⟩, ⟨.and, [12, 13]⟩, ⟨.or, [14, 7]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000000000000000 0x0000000000000000 0x66c1006000800785 0xacd8200c001000f0

def z1 : W := mkw 0x01000000a00282ac 0x0020000014005055 0xfec14463e08f87ff 0xbfd8288c7c11f0ff

def z2 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xbda6ba5d87766667 0x77b4d74bb0eecccc

def z3 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x67df03e01f807f85 0xecfbe07c03f00ff0

def z4 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x1fbffc001fff8003 0xe3f7ff8003fff000

def z5 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0xebf8c39e1878787e 0xfd7f1873c30f0f0f

def z6 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xffdfffffe0800785 0xbffbfffffc1000f0

def z7 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0x0178839c1878787e 0xe02f1073830f0f0f

def z8 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xff9fffffe0000000 0x1ff3fffffc000000

def z9 : W := mkw 0xc01df5bb40000000 0xd803beb768000000 0xda19fdbfe0000000 0x1b433fb7fc000000

def z10 : W := mkw 0x0800000015805500 0x0100000002b00aa0 0x004000001f807f85 0xe008000003f00ff0

def z11 : W := mkw 0x0815012014801100 0x0102a02402900220 0x425901a018801980 0x884b203403100330

def z12 : W := mkw 0xc81ff7fb55805500 0xf903feff6ab00aa0 0xffdfffffff807f85 0xfffbfffffff00ff0

def z13 : W := mkw 0xca3fffffd7b67766 0xf947fffffaf6ceec 0xfffffffffff67fe7 0xfffffffffffecffc

def z14 : W := mkw 0x001de40014800000 0xc003bc8002900000 0x1f9ffc001f800001 0xe3f3ff8003f00000

def z15 : W := mkw 0x30152c001eed0000 0x4602a58003dda000 0x14273c001fff8003 0xe284e78003fff000

def z16 : W := mkw 0x8008c09200000000 0x9001181240000000 0xeb98c39e00000000 0x1d731873c0000000

def z17 : W := mkw 0x0000080002240000 0x0000010000448000 0x1fa7fc0007ff8003 0xe3f4ff8000fff000

def z18 : W := mkw 0x03221a4da336e6ee 0x20644349b466dcdd 0xffe7fe7fe7ffe7ff 0xfffcffcffcfffcff

def z19 : W := mkw 0xa62adadf0b7c6c52 0xb4c55b5be16f8d8a 0xebfefb9e1f78787e 0xfd7fdf73c3ef0f0f

def z20 : W := mkw 0x0000000001004400 0x0000000000200880 0x0000000007006605 0x6000000000e00cc0

def z21 : W := mkw 0x0815012014801100 0x0102a02402900220 0x63d903a018807984 0xec7b207403100f30

def z22 : W := mkw 0xc01de5b240000000 0xd803bcb648000000 0x421945a260000000 0x084328b44c000000

def z23 : W := mkw 0xf01dedb25eed0000 0xde03bdb64bdda000 0x5fbffda27fff8003 0xebf7ffb44ffff000

def z24 : W := mkw 0x02221a4d03346442 0x20444349a0668c88 0x0126ba1c07706000 0x4024d74380ee0c00

def z25 : W := mkw 0xc008f49b40000000 0xd8011e9368000000 0x9800fc1fe0000000 0x13001f83fc000000

def z26 : W := mkw 0x09170360b582d7ac 0x2122e06c16b05af5 0xffdf47e3ff8fffff 0xfffbe8fc7ff1ffff

def z27 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0x0138839c18707800 0x40271073830e0f00

def z28 : W := mkw 0xb41dec961efd2850 0xd683bd92c3dfa50a 0xffffff9e1ffff87f 0xfffffff3c3ffff0f

def z29 : W := mkw 0xc00af6db40000000 0xf8015edb68000000 0xbd86fe5fe0000000 0x17b0dfcbfc000000

def z30 : W := mkw 0x0000000000000000 0x0000000000000000 0xfe814463e08f8003 0xbfd0288c7c11f000

def z31 : W := mkw 0x2400000408582850 0x04800000810b050a 0x006000001878787e 0xe00c0000030f0f0f

def z32 : W := mkw 0xe41ff7ff48582850 0xfc83feffe90b050a 0xfffffffff878787e 0xffffffffff0f0f0f

def z33 : W := mkw 0x0800000015805500 0x0100000002b00aa0 0x63d803801f807f85 0xec7b007003f00ff0

def z34 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0xfff9c79e18fff87f 0xffff38f3c31fff0f

def z35 : W := mkw 0x8008c09200000000 0x9001181240000000 0x8800c01e00000000 0x11001803c0000000

def z36 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x013eb8001f700000 0x4027d70003ee0000

def z37 : W := mkw 0x0000000000000000 0x0000000000000000 0xeac040020008007e 0xbd5808004001000f

def z38 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x0407006007800781 0x0080e00c00f000f0

def z39 : W := mkw 0x01000000a00282ac 0x0020000014005055 0x9c014463e08f87fb 0x1380288c7c11f0ff

def z40 : W := mkw 0x0220180d02342042 0x00440301a0468408 0x0020b81c00700000 0x00041703800e0000

def z41 : W := mkw 0xc81ff7fb55805500 0xf903feff6ab00aa0 0x67dfbbfc1f807f85 0xecfbf77f83f00ff0

def z42 : W := mkw 0x0220180d82362266 0x00440301b046c44c 0x9820b81d80760062 0x13041703b00ec00c

def z43 : W := mkw 0x301de4001cc90000 0xc603bc8003992000 0x0219440018898000 0x8043288003113000

def z44 : W := mkw 0x0015000000000000 0x0002a00000000000 0x079f000000000000 0x00f3e00000000000

def z45 : W := mkw 0xa508c096a85aaafc 0x94a11812d50b555f 0xfff9c7fff8ffffff 0xffff38ffff1fffff

def z46 : W := mkw 0x0222124d81126666 0x20444249b0224ccc 0xa000025d80006664 0x1400004bb0000ccc

def z47 : W := mkw 0xf01ff7fb5cc90000 0xfe03feff6b992000 0xff9ffffff8898000 0x9ff3ffffff113000

def z48 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0x9c26b85d87760663 0x1384d70bb0eec0cc

def z49 : W := mkw 0x301dec000a6d0000 0xc603bd80014da000 0x1fbffc00007f8002 0x03f7ff80000ff000

def z50 : W := mkw 0xc01ff7fbc0020224 0xf803feff78004044 0xff9fffffe0060667 0x3ff3fffffc00c0cc

def z51 : W := mkw 0x0000000000000000 0x0000000000000000 0x6040006000000784 0x0c08000c000000f0

def z52 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0x991eff9fe0000000 0x1323dff3fc000000

def z53 : W := mkw 0x0000000000000000 0x0000000000000000 0x1e814400008f8003 0xa3d028800011f000

def z54 : W := mkw 0x0000080002240000 0x0000010000448000 0x1da6b80007760003 0x63b4d70000eec000

def z55 : W := mkw 0x0a20080497b67766 0x0144010092f6ceec 0x006000001ff67fe7 0xe00c000003fecffc

def z56 : W := mkw 0x0802036001005500 0x2100406c00200aa0 0x604003e000007f84 0x0c08007c00000ff0

def z57 : W := mkw 0x3008ec000a6d0000 0xc6011d80014da000 0x1820fc00007f8002 0x03041f80000ff000

def z58 : W := mkw 0x281fc3601dc85500 0xa503f86c03b90aa0 0x6fffc3e01ff87f87 0xedfff87c03ff0ff0

def z59 : W := mkw 0x2008c00008480000 0x8401180001090000 0x0bb8c00018780002 0xe1771800030f0000

def z60 : W := mkw 0xe01ff7fb48480000 0xfc03feff69090000 0xffbffffff8780002 0xfff7ffffff0f0000

def z61 : W := mkw 0x0000080402342040 0x0000010080468408 0xbda6ba1c07766067 0x77b4d74380eecc0c

def z62 : W := mkw 0x10152c0016a50000 0x4202a58002d4a000 0x14073c0007878001 0x0280e78000f0f000

def z63 : W := mkw 0x8400009600102850 0x10800012c002050a 0xe040039e0000787c 0x1c080073c0000f0f

def z64 : W := mkw 0x0000000080020224 0x0000000010004044 0xbc80004180060667 0x379000083000c0cc

def z65 : W := mkw 0x0100000020008088 0x0020000004001011 0x4241442260898198 0x884828844c113033

def z66 : W := mkw 0x08170b6017a45500 0x2102e16c02f48aa0 0x7fffbbe01ff67f87 0xeffff77c03fecff0

def z67 : W := mkw 0xd01ffffb56a50000 0xfa03ffff6ad4a000 0xff9fffffe7878001 0x1ff3fffffcf0f000

def z68 : W := mkw 0x0322124da112e6ee 0x20644249b4225cdd 0xe040027fe00067fc 0x1c08004ffc000cff

def z69 : W := mkw 0x01000000a00282ac 0x0020000014005055 0x14010461e0878781 0x0280208c3c10f0f0

def z70 : W := mkw 0xc11ff7fbe00282ac 0xf823feff7c005055 0xffdfffffe08f87ff 0xbffbfffffc11f0ff

def z71 : W := mkw 0x081fe76015805500 0xe103fcec02b00aa0 0x7fdfffe01f807f85 0xeffbfffc03f00ff0

def z72 : W := mkw 0x0002124900000000 0x2000424920000000 0xbd86ba5d80000000 0x17b0d74bb0000000

def z73 : W := mkw 0x0000000000000000 0x0000000000000000 0xea80400200000000 0x1d50080040000000

def z74 : W := mkw 0xc81ff7fb55805500 0xf903feff6ab00aa0 0xff9fffffe7800781 0x1ff3fffffcf000f0

def z75 : W := mkw 0x03221a4da336e6ee 0x20644349b466dcdd 0xbde6ba5d87ffe7ff 0xf7bcd74bb0fffcff

def z76 : W := mkw 0x0000000400102040 0x0000000080020408 0xa9a0821c00706066 0x75341043800e0c0c

def z77 : W := mkw 0xa508c096a85aaafc 0x94a11812d50b555f 0x9820c41fe07f807a 0x13041883fc0ff00f

def z78 : W := mkw 0xc81ff7fb55805500 0xf903feff6ab00aa0 0x011ebb9c1f007800 0x4023d77383e00f00

def z79 : W := mkw 0x02221a4d82362266 0x20444349b046c44c 0xbda6ba5d80760062 0x17b4d74bb00ec00c

def z80 : W := mkw 0x2000000008480000 0x0400000001090000 0x0020000018780002 0xe0040000030f0000

def z81 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0x8820c01e0078007a 0x11041803c00f000f

def z82 : W := mkw 0x85000096a012aafc 0x10a00012d402555f 0xe04003ffe0007ffc 0x1c08007ffc000fff

def z83 : W := mkw 0x00021a4902240000 0x2000434920448000 0xbda6ba5d87760003 0x77b4d74bb0eec000

def z84 : W := mkw 0x26221a4d8b7e6e76 0x24c44349b16fcdce 0xbde6ba5d9f7e7e7f 0xf7bcd74bb3efcfcf

def z85 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0x4378c39e18787818 0xc86f1873c30f0f03

def z86 : W := mkw 0x301fef601eed0000 0xe603fdec03dda000 0x7fbfffe01fff8003 0xeff7fffc03fff000

def z87 : W := mkw 0x01000000a00282ac 0x0020000014005055 0xe0400063e08f87ff 0xbc08000c7c11f0ff

def z88 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xa126ba5d87706664 0x5424d74bb0ee0ccc

def z89 : W := mkw 0x4017376940000000 0x6802e6ed28000000 0x0006380000000000 0x0000c70000000000

def z90 : W := mkw 0x0000000000000000 0x0000000000000000 0xfe814463e0000000 0x1fd0288c7c000000

def z91 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x013eb8001fff8003 0xe027d70003fff000

def z92 : W := mkw 0x50173f6956a50000 0x6a02e7ed2ad4a000 0x14073c61e7878001 0x0280e78c3cf0f000

def z93 : W := mkw 0x03221a49a326c6ae 0x206443493464d8d5 0x14073c61e7878781 0x0280e78c3cf0f0f0

def z94 : W := mkw 0x0800000015805500 0x0100000002b00aa0 0x66c100601f807f85 0xecd8200c03f00ff0

def z95 : W := mkw 0x011de400a00282ac 0xc023bc8014005055 0xffdffc63e08f87ff 0xbffbff8c7c11f0ff

def z96 : W := mkw 0x25000004a85aaafc 0x04a00000950b555f 0x0060000018ffffff 0xe00c0000031fffff

def z97 : W := mkw 0x09170360b582d7ac 0x2122e06c16b05af5 0x77df07e1ff87ff85 0xeefbe0fc3ff0fff0

def z98 : W := mkw 0xc11ff7fbe00282ac 0xf823feff7c005055 0xff9fffffe0878781 0x1ff3fffffc10f0f0

def z99 : W := mkw 0x311de400bccb82ac 0xc623bc8017997055 0xfed94463f88f87ff 0xbfdb288c7f11f0ff

def z100 : W := mkw 0x2008c00008480000 0x8401180001090000 0x0218400018080000 0x8043080003010000

def z101 : W := mkw 0x0800000001005500 0x0100000000200aa0 0x0040000000007f84 0x0008000000000ff0

def z102 : W := mkw 0x300008001eed0000 0x0600010003dda000 0x002000001fff8003 0xe004000003fff000

def z103 : W := mkw 0xf01ffffb5eed0000 0xfe03ffff6bdda000 0xffbfffffffff8003 0xfff7fffffffff000

def z104 : W := mkw 0x822adadf83366666 0xb0455b5bf066cccc 0xffbefbdf87766667 0x7ff7df7bf0eecccc

def z105 : W := mkw 0x0002124900000000 0x2000424920000000 0xff87fe7fe0000000 0x1ff0ffcffc000000

def z106 : W := mkw 0x311dec00beef82ac 0xc623bd8017ddf055 0xfffffc63ffff87ff 0xffffff8c7ffff0ff

def z107 : W := mkw 0x0000000000000000 0x0000000000000000 0x67d903e018807f85 0xecfb207c03100ff0

def z108 : W := mkw 0x0a371b6997a65726 0x2146e36d32f4cae4 0x1407386187860781 0x0280e70c30f0c0f0

def z109 : W := mkw 0x0000000000000000 0x0000000000000000 0x63d8038018007804 0xec7b007003000f00

def z110 : W := mkw 0x01000000a00282ac 0x0020000014005055 0xffd947e3f88fffff 0xfffb28fc7f11ffff

def z111 : W := mkw 0xc008f49b40000000 0xd8011e9368000000 0xfb98ff9fe0000000 0x1f731ff3fc000000

def z112 : W := mkw 0x41173769e00282ac 0x6822e6ed3c005055 0xfec77c63e08f87ff 0xbfd8ef8c7c11f0ff

def z113 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x435f03a01f807980 0xc86be07403f00f30

def z114 : W := mkw 0x0100000020008088 0x0020000004001011 0x0040000000898198 0x8008000000113033

def z115 : W := mkw 0x0000000000000000 0x0000000000000000 0x98004403e0000000 0x130008807c000000

def z116 : W := mkw 0x0017036000000000 0x2002e06c00000000 0x67df03e000800785 0xacfbe07c001000f0

def z117 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0xebb8c39e18707800 0x5d771873c30e0f00

def z118 : W := mkw 0xa408c096885a2a74 0x94811812d10b454e 0xfff8c3df987e7e7f 0xffff187bf30fcfcf

def z119 : W := mkw 0x01000000a00282ac 0x0020000014005055 0x98004403e00f807a 0x130008807c01f00f

def z120 : W := mkw 0xb41dec921eed0810 0xd683bd9243dda102 0x5ffffd821fff981b 0xebffffb043fff303

def z121 : W := mkw 0x0220080483366666 0x004401009066cccc 0x0020000007766667 0x6004000000eecccc

def z122 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z123 : W := mkw 0xa62adadf8b7e6e76 0xb4c55b5bf16fcdce 0xfffefbdf9f7e7e7f 0xffffdf7bf3efcfcf

def z124 : W := mkw 0x0100000020008088 0x0020000004001011 0xfec14463e0898198 0x9fd8288c7c113033

def z125 : W := mkw 0xe41ff7ff48582850 0xfc83feffe90b050a 0xffbfffffe078007a 0x1ff7fffffc0f000f

def z126 : W := mkw 0xb41de4921cc90810 0xd683bc9243992102 0x4259458218899818 0x884b28b043113303

def z127 : W := mkw 0xa408c09208480810 0x9481181241090102 0x0018018018001800 0x0003003003000300

def z128 : W := mkw 0x381fef601fed5500 0xe703fdec03fdaaa0 0x1fbfff801ffff803 0xe3f7fff003ffff00

def z129 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x011e03801f007800 0x4023c07003e00f00

def z130 : W := mkw 0x0002024001004400 0x2000404800200880 0x2586024007006605 0x64b0c04800e00cc0

def z131 : W := mkw 0xc01ff7fb41004400 0xf803feff68200880 0xff9fffffe7006605 0x7ff3fffffce00cc0

def z132 : W := mkw 0x01000800a22682ac 0x002001001444d055 0xffe7fc63e7ff87ff 0xfffcff8c7cfff0ff

def z133 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0xebb8c39e0078007a 0x1d771873c00f000f

def z134 : W := mkw 0x0802036001005500 0x2100406c00200aa0 0x63d803e018007f84 0xec7b007c03000ff0

def z135 : W := mkw 0x301de4001cc90000 0xc603bc8003992000 0x1e994400188f8003 0xa3d328800311f000

def z136 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x0006000007000000 0x0000c00000e00000

def z137 : W := mkw 0xc23fffffc3366666 0xf847fffff866cccc 0xffbfffffe7766667 0x7ff7fffffceecccc

def z138 : W := mkw 0x2c0000041dd87d50 0x0580000083bb0faa 0x006000001ff87fff 0xe00c000003ff0fff

def z139 : W := mkw 0x701fff695eed0000 0xee03ffed2bdda000 0x1fbffc61ffff8003 0xe3f7ff8c3ffff000

def z140 : W := mkw 0x4017376940000000 0x6802e6ed28000000 0x14073c61e0000000 0x0280e78c3c000000

def z141 : W := mkw 0x10152c0016a50000 0x4202a58002d4a000 0x1da7bc0007f78003 0x63b4f78000fef000

def z142 : W := mkw 0xac1fc3f61dd87d50 0xb583f87ec3bb0faa 0xefffc3fe1ff87fff 0xfdfff87fc3ff0fff

def z143 : W := mkw 0x01020240a102c6ac 0x20204048142058d5 0xffc74663e78fe7ff 0xfff8e8cc7cf1fcff

def z144 : W := mkw 0xac1dc1b21cc81910 0x9583b83643990322 0x425941a218881998 0x884b283443110333

def z145 : W := mkw 0x8008c09200000000 0x9001181240000000 0xebd8c39e18007804 0xfd7b1873c3000f00

def z146 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x644703e007807f85 0x0c88e07c00f00ff0

def z147 : W := mkw 0x18172f6017a55500 0x6302e5ec02f4aaa0 0x77df3fe01f87ff85 0xeefbe7fc03f0fff0

def z148 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0x0020801c00700000 0x00041003800e0000

def z149 : W := mkw 0x02371a4d97b66666 0x2046e349b2f6cccc 0xbfbfba5d9ff66667 0xf7f7f74bb3fecccc

def z150 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xffe7ba7d87f667e7 0xfffcf74fb0feccfc

def z151 : W := mkw 0x001de40000000000 0xc003bc8000000000 0x0219440000000000 0x0043288000000000

def z152 : W := mkw 0x0000000000000000 0x0000000000000000 0x4201442260000000 0x084028844c000000

def z153 : W := mkw 0x0800000015805500 0x0100000002b00aa0 0x000000001f007800 0x4000000003e00f00

def z154 : W := mkw 0xa508c09228488898 0x94a1181245091113 0x425945a278899998 0x884b28b44f113333

def z155 : W := mkw 0x8008c09200000000 0x9001181240000000 0xebd8c39e0008007e 0xbd7b1873c001000f

def z156 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x023944001fff8003 0xe047288003fff000

def z157 : W := mkw 0x03200804a336e6ee 0x006401009466dcdd 0xfee14463e7ffe7ff 0xffdc288c7cfffcff

def z158 : W := mkw 0xa41fc3f608582850 0xb483f87ec10b050a 0xefffc3fe1878787e 0xfdfff87fc30f0f0f

def z159 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x193efc001f7f8002 0x4327df8003eff000

def z160 : W := mkw 0x381fef601fed5500 0xe703fdec03fdaaa0 0x7fffffe01fffff87 0xeffffffc03fffff0

def z161 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0x1526ba5d87766601 0x42a4d74bb0eeccc0

def z162 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0x0126ba1c07766667 0x6024d74380eecccc

def z163 : W := mkw 0x0000100900000000 0x0000020120000000 0x9800b81d80000000 0x13001703b0000000

def z164 : W := mkw 0x300000001cc90000 0x0600000003992000 0x0000000018898000 0x8000000003113000

def z165 : W := mkw 0x323ffe4d9fff6666 0xe647ffc9b3ffeccc 0xbdbeba5d9f766667 0x77b7d74bb3eecccc

def z166 : W := mkw 0xc01fe7f240000000 0xf803fcfe48000000 0x679f47e260000000 0x0cf3e8fc4c000000

def z167 : W := mkw 0x01021249a00282ac 0x2020424934005055 0xffc7fe7fe08f87ff 0xbff8ffcffc11f0ff

def z168 : W := mkw 0xe408f49f48582850 0xdc811e93e90b050a 0xfbf8ff9ff878787e 0xff7f1ff3ff0f0f0f

def z169 : W := mkw 0xe408f49f48582850 0xdc811e93e90b050a 0x9820fc1fe078007a 0x13041f83fc0f000f

def z170 : W := mkw 0x02221a4d03346442 0x20444349a0668c88 0x1da6ba1c07766003 0x63b4d74380eecc00

def z171 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0xa9a0c21e0078607e 0x75341843c00f0c0f

def z172 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0x1f9fff9c00000000 0x03f3fff380000000

def z173 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xfffebbdd9f767e67 0xffffd77bb3eecfcc

def z174 : W := mkw 0xe41de5b248480810 0xdc83bcb649090102 0x425945a278081818 0x884b28b44f010303

def z175 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0xa9b8839c18707866 0x75371073830e0f0c

def z176 : W := mkw 0x0a371b6d97b67766 0x2146e36db2f6ceec 0xffffbbfd9ff67fe7 0xfffff77fb3fecffc

def z177 : W := mkw 0x0815012015805500 0x0102a02402b00aa0 0x425901a01f807f85 0xe84b203403f00ff0

def z178 : W := mkw 0xf01dfc9b5eed0000 0xde03bf936bdda000 0x9fbffc1fffff8003 0xf3f7ff83fffff000

def z179 : W := mkw 0x323ffe4d9fff6666 0xe647ffc9b3ffeccc 0xbfbffe5d9fffe667 0xf7f7ffcbb3fffccc

def z180 : W := mkw 0x001fe76000000000 0xe003fcec00000000 0x7f9fffe000000000 0x0ff3fffc00000000

def z181 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xa020025d87766667 0x7404004bb0eecccc

def z182 : W := mkw 0xc00213fb40000000 0x3800427f68000000 0xe00003ffe0000000 0x1c00007ffc000000

def z183 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0x1426384187766667 0x6284c70830eecccc

def z184 : W := mkw 0x0002124d00102040 0x20004249a0020408 0xbda6ba5d80706066 0x77b4d74bb00e0c0c

def z185 : W := mkw 0x0b371b6db7b6f7ee 0x2166e36db6f6defd 0xffffffffffffffff 0xffffffffffffffff

def z186 : W := mkw 0x0000000000000000 0x0000000000000000 0x18004400000f8002 0x030008800001f000

def z187 : W := mkw 0x01000000a00282ac 0x0020000014005055 0xe0400063e00007fc 0x1c08000c7c0000ff

def z188 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0xfffffc021fff807f 0xffffff8043fff00f

def z189 : W := mkw 0x0a371b6d17b47542 0x2146e36da2f68ea8 0x013ebb9c1f707800 0x4027d77383ee0f00

def z190 : W := mkw 0x0100000020008088 0x0020000004001011 0x5ec14422608f819b 0xabd828844c11f033

def z191 : W := mkw 0x0015000014800000 0x0002a00002900000 0x079f00001f800001 0xe0f3e00003f00000

def z192 : W := mkw 0x0000000000000000 0x0000000000000000 0x1e81440000000000 0x03d0288000000000

def z193 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x1a39fc0018ff8002 0x83473f80031ff000

def z194 : W := mkw 0x001de40000000000 0xc003bc8000000000 0x1f9ffc0000000000 0x03f3ff8000000000

def z195 : W := mkw 0xf01de5b25cc90000 0xde03bcb64b992000 0x421945a278898000 0x884328b44f113000

def z196 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x615e03e01f007f84 0x4c2bc07c03e00ff0

def z197 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xe11ebbffe0000000 0x1c23d77ffc000000

def z198 : W := mkw 0x3008c8001eed0000 0x8601190003dda000 0x0bb8c0001fff8003 0xe177180003fff000

def z199 : W := mkw 0xa508c096a85aaafc 0x94a11812d50b555f 0xebf8c39e18ffffff 0xfd7f1873c31fffff

def z200 : W := mkw 0x0000000000000000 0x0000000000000000 0x6398038000000000 0x0c73007000000000

def z201 : W := mkw 0x0815012014801100 0x0102a02402900220 0x0018018018001800 0x0003003003000300

def z202 : W := mkw 0x0220080483366666 0x004401009066cccc 0xbca0004187766667 0x7794000830eecccc

def z203 : W := mkw 0x02221a4983264626 0x204443493064c8c4 0x1406384187060601 0x0280c70830e0c0c0

def z204 : W := mkw 0xa408c09208480810 0x9481181241090102 0x4258418218081818 0x884b083043010303

def z205 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0x9926ba1d87766062 0x5324d743b0eecc0c

def z206 : W := mkw 0x2008c00008480000 0x8401180001090000 0xebf8c0021878007e 0xfd7f1800430f000f

def z207 : W := mkw 0x3228fc0d8a7f2266 0xc6451f81b14fe44c 0x9820fc1d807f8062 0x13041f83b00ff00c

def z208 : W := mkw 0x01000000a00282ac 0x0020000014005055 0x14410461e08f87ff 0xa288208c3c11f0ff

def z209 : W := mkw 0x0017036000000000 0x2002e06c00000000 0x679f03e000000000 0x0cf3e07c00000000

def z210 : W := mkw 0x0015000014800000 0x0002a00002900000 0x0219000018800000 0x8043200003100000

def z211 : W := mkw 0xc01df49b40000000 0xd803be9368000000 0x9f9ffc1fe0000000 0x13f3ff83fc000000

def z212 : W := mkw 0xec1ff7ff5dd87d50 0xfd83feffebbb0faa 0xfffffffffff87fff 0xffffffffffff0fff

def z213 : W := mkw 0x2400000408582850 0x04800000810b050a 0x63f803801878787e 0xec7f0070030f0f0f

def z214 : W := mkw 0xc01737fb40000000 0x7802e6ff68000000 0xf4073fffe0000000 0x1e80e7fffc000000

def z215 : W := mkw 0x322008049fff6666 0x0644010093ffeccc 0x002000001fffe667 0xe004000003fffccc

def z216 : W := mkw 0xc81de5b254801100 0xd903bcb64a900220 0x425945a278801980 0x884b28b44f100330

def z217 : W := mkw 0xc33fffffe336e6ee 0xf867fffffc66dcdd 0xffffffffe7ffe7ff 0xfffffffffcfffcff

def z218 : W := mkw 0x03200804a336e6ee 0x006401009466dcdd 0x0060000007ffe7ff 0xe00c000000fffcff

def z219 : W := mkw 0x03221a4da336e6ee 0x20644349b466dcdd 0xbda6fe5fe77fe67f 0x77b4dfcbfceffccf

def z220 : W := mkw 0x0000000000000000 0x0000000000000000 0x880040020008007a 0x110008004001000f

def z221 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0x151fbffde0000000 0x02a3f7ffbc000000

def z222 : W := mkw 0x0a370b6497b67766 0x2146e16c92f6ceec 0x67ff03e01ff67fe7 0xecffe07c03fecffc

def z223 : W := mkw 0x0002124900000000 0x2000424920000000 0x1406384180000000 0x0280c70830000000

def z224 : W := mkw 0x0002024081024624 0x20004048102048c4 0xbd86024187066667 0x77b0c04830e0cccc

def z225 : W := mkw 0xc008f49b40000000 0xd8011e9368000000 0xfe81fc7fe0000000 0x1fd03f8ffc000000

def z226 : W := mkw 0x2008c00008480000 0x8401180001090000 0x0138800018700000 0x40271000030e0000

def z227 : W := mkw 0x2400000408582850 0x04800000810b050a 0x0020000018707800 0x40040000030e0f00

def z228 : W := mkw 0x001de40000000000 0xc003bc8000000000 0x1f9ffc00008f8003 0xa3f3ff800011f000

def z229 : W := mkw 0x0000000080020224 0x0000000010004044 0xbe814441808f8667 0xb7d028883011f0cc

def z230 : W := mkw 0xf23fffffdfff6666 0xfe47fffffbffeccc 0xffbfffffffffe667 0xfff7fffffffffccc

def z231 : W := mkw 0x0000000000000000 0x0000000000000000 0x0398000018000000 0xe073000003000000

def z232 : W := mkw 0x0a221b6d83367766 0x2144436db066ceec 0xfde6bbfd87767fe7 0x7fbcd77fb0eecffc

def z233 : W := mkw 0x3008ec000a6d0000 0xc6011d80014da000 0x1bb8fc00187f8002 0xe3771f80030ff000

def z234 : W := mkw 0x401ff76940000000 0xe803feed28000000 0x1f9ffc61e0000000 0x03f3ff8c3c000000

def z235 : W := mkw 0x323ffe4d1ffd6442 0xe647ffc9a3ffac88 0x1fbffe1c1fffe003 0xe3f7ffc383fffc00

def z236 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x7fdf47e01f8fff87 0xeffbe8fc03f1fff0

def z237 : W := mkw 0x0222124d81126666 0x20444249b0224ccc 0xbc80025d80066667 0x3790004bb000cccc

def z238 : W := mkw 0x03221a4da336e6ee 0x20644349b466dcdd 0xbda7be7de7f7e7e7 0x77b4f7cfbcfefcfc

def z239 : W := mkw 0x3008ec000a6d0000 0xc6011d80014da000 0x1da6fc00077f8003 0x63b4df8000eff000

def z240 : W := mkw 0x2008c8000a6c0000 0x84011900014d8000 0x1fbef8001f7e0003 0xe3f7df0003efc000

def z241 : W := mkw 0x2108c000a84a82ac 0x8421180015095055 0xfff9c463f8ff87ff 0xffff388c7f1ff0ff

def z242 : W := mkw 0x0000000000000000 0x0000000000000000 0x0a80400000080002 0xa150080000010000

def z243 : W := mkw 0x3108ec00aa6f82ac 0xc6211d80154df055 0x9820fc03e07f807a 0x13041f807c0ff00f

def z244 : W := mkw 0x01000000a00282ac 0x0020000014005055 0xf8404463e00f87fe 0x1f08088c7c01f0ff

def z245 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0xffdf47e3ff807f85 0xfffbe8fc7ff00ff0

def z246 : W := mkw 0xc41ff7ff40102850 0xf883feffe802050a 0xffdfffffe000787c 0x1ffbfffffc000f0f

def z247 : W := mkw 0x0915012034809188 0x0122a02406901231 0x425945a278899998 0x884b28b44f113333

def z248 : W := mkw 0xb41dec961efd2850 0xd683bd92c3dfa50a 0xebfefb9e1f78787e 0xfd7fdf73c3ef0f0f

def z249 : W := mkw 0x01000000a00282ac 0x0020000014005055 0xfec14463e00007fc 0x1fd8288c7c0000ff

def z250 : W := mkw 0x0015000014800000 0x0002a00002900000 0x1f9f44001f8f8003 0xe3f3e88003f1f000

def z251 : W := mkw 0x4017376940000000 0x6802e6ed28000000 0xfe877c63e0000000 0x1fd0ef8c7c000000

def z252 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0x011ebb9c00000000 0x0023d77380000000

def z253 : W := mkw 0x300008001eed0000 0x0600010003dda000 0x1da6b8001fff8003 0xe3b4d70003fff000

def z254 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xbfa7fe5d87ffe667 0xf7f4ffcbb0fffccc

def z255 : W := mkw 0x0220180d82362266 0x00440301b046c44c 0x9da6b81d87760063 0x73b4d703b0eec00c

def z256 : W := mkw 0x0002024401106440 0x2000404880220c88 0xada6825c07706667 0x75b4d04b80ee0ccc

def z257 : W := mkw 0x01000000a00282ac 0x0020000014005055 0xeac04002008f87ff 0xbd5808004011f0ff

def z258 : W := mkw 0x323dec049fff6666 0xc647bd8093ffeccc 0x1fbffc001fffe667 0xe3f7ff8003fffccc

def z259 : W := mkw 0x0000000000000000 0x0000000000000000 0x4241002000800180 0x8848200400100030

def z260 : W := mkw 0x0a371b6d17b47542 0x2146e36da2f68ea8 0x67ffbbfc1ff07f85 0xecfff77f83fe0ff0

def z261 : W := mkw 0xa508c092a84a8abc 0x94a1181255095157 0xfed945e3f88f9fff 0xbfdb28bc7f11f3ff

def z262 : W := mkw 0x0800000014801100 0x0100000002900220 0x0040000018801980 0x8008000003100330

def z263 : W := mkw 0xc23ff7ffc1126666 0xf847fefff8224ccc 0xff9fffffe0006664 0x1ff3fffffc000ccc

def z264 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x161f7c001f8f8001 0x82c3ef8003f1f000

def z265 : W := mkw 0xc01ff7fb54800000 0xf803feff6a900000 0xff9fffffff800001 0xfff3fffffff00000

def z266 : W := mkw 0x0000000000000000 0x0000000000000000 0x62c0000000000004 0xac58000000000000

def z267 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0x431fffbe60000000 0x0863fff7cc000000

def z268 : W := mkw 0x0000000080020224 0x0000000010004044 0xfec10061808607e7 0xbfd8200c3010c0fc

def z269 : W := mkw 0x0100000020008088 0x0020000004001011 0x66c144626089879d 0xacd8288c4c1130f3

def z270 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x259e03c01f007e05 0x64b3c07803e00fc0

def z271 : W := mkw 0xac08c0961dd87d50 0x95811812c3bb0faa 0xebf8c39e1ff87fff 0xfd7f1873c3ff0fff

def z272 : W := mkw 0xc01de5b240000000 0xd803bcb648000000 0xfe9945e3e0000000 0x1fd328bc7c000000

def z273 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xffa7fe7fe7766667 0x7ff4ffcffceecccc

def z274 : W := mkw 0x0220100d80122266 0x00440201b002444c 0x8000001d80000060 0x10000003b000000c

def z275 : W := mkw 0x0100000020008088 0x0020000004001011 0xeac14422608981fe 0xbd5828844c11303f

def z276 : W := mkw 0x2c1703641dd87d50 0x2582e06c83bb0faa 0x67ff03e01ff87fff 0xecffe07c03ff0fff

def z277 : W := mkw 0x0015012000000000 0x0002a02400000000 0x421901a000000000 0x0843203400000000

def z278 : W := mkw 0x0008c00000000000 0x8001180000000000 0x0b98c00000000000 0x0173180000000000

def z279 : W := mkw 0x0002124900000000 0x2000424920000000 0xa000025d80000000 0x1400004bb0000000

def z280 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0xe860c39e0078787e 0x1d0c1873c00f0f0f

def z281 : W := mkw 0x0a221a4d97b67766 0x21444349b2f6ceec 0xbde6ba5d9ff67fe7 0xf7bcd74bb3fecffc

def z282 : W := mkw 0xc10213fbe00282ac 0x3820427f7c005055 0xfec147ffe08f87ff 0xbfd828fffc11f0ff

def z283 : W := mkw 0xc00213fb40000000 0x3800427f68000000 0x0000039c00000000 0x0000007380000000

def z284 : W := mkw 0x0002024001004400 0x2000404800200880 0x0406004007000601 0x0080c00800e000c0

def z285 : W := mkw 0x01000000a00282ac 0x0020000014005055 0xeac04063e00807fe 0xbd58080c7c0100ff

def z286 : W := mkw 0xa41de49608582850 0xd483bc92c10b050a 0xffffff9e1878787e 0xfffffff3c30f0f0f

def z287 : W := mkw 0x12373e4d97b76666 0x6246e7c9b2f6eccc 0xbda7be5d87f7e667 0x77b4f7cbb0fefccc

def z288 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xffe6fa5f877e667f 0xfffcdf4bf0efcccf

def z289 : W := mkw 0x01000000a00282ac 0x0020000014005055 0x00400000008f87ff 0xa00800000011f0ff

def z290 : W := mkw 0x02221a4d03346442 0x20444349a0668c88 0xbda6ba5d87706000 0x57b4d74bb0ee0c00

def z291 : W := mkw 0xa40ac2d609586c50 0xb481585ac12b0d8a 0xeffec3de1f787e7f 0xfdffd87bc3ef0fcf

def z292 : W := mkw 0x0000000400102040 0x0000000080020408 0xebf8839c18707866 0xfd7f1073830e0f0c

def z293 : W := mkw 0xe41ff7fb48480810 0xfc83feff69090102 0xffdffffff8081818 0x9ffbffffff010303

def z294 : W := mkw 0x0817136915805500 0x2102e26d22b00aa0 0xffdfbbfd9f807f85 0xfffbf77fb3f00ff0

def z295 : W := mkw 0x0017036014800000 0x2002e06c02900000 0x679f03e01f800001 0xecf3e07c03f00000

def z296 : W := mkw 0x4017376940000000 0x6802e6ed28000000 0xbd87be7de0000000 0x17b0f7cfbc000000

def z297 : W := mkw 0x03221a4da336e6ee 0x20644349b466dcdd 0xfde6ba7fe77667ff 0x7fbcd74ffceeccff

def z298 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0xfff9c7fff878787e 0xffff38ffff0f0f0f

def z299 : W := mkw 0x2008c00008480000 0x8401180001090000 0x0820c00000780002 0x01041800000f0000

def z300 : W := mkw 0x0320180da236a2ee 0x00640301b446d45d 0xfee1fc7fe0ff87ff 0xbfdc3f8ffc1ff0ff

def z301 : W := mkw 0x02371b6d83366666 0x2046e36db066cccc 0xffbfbbfd87766667 0x7ff7f77fb0eecccc

def z302 : W := mkw 0x0220180d83366666 0x00440301b066cccc 0x9820b81d87766667 0x73041703b0eecccc

def z303 : W := mkw 0x0a22136d81127766 0x2144426db0224eec 0xe04003fd80007fe4 0x1c08007fb0000ffc

def z304 : W := mkw 0xb01dec921eed0000 0xd603bd9243dda000 0xffbfff9e1fff8003 0xfff7fff3c3fff000

def z305 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xbd9ebbdd80000000 0x17b3d77bb0000000

def z306 : W := mkw 0xc01ffffb42240000 0xf803ffff68448000 0xffbfffffe7760003 0x7ff7fffffceec000

def z307 : W := mkw 0x0000080002240000 0x0000010000448000 0x0020000007760003 0x6004000000eec000

def z308 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0xeff9c3fe18f87fff 0xfdff387fc31f0fff

def z309 : W := mkw 0xe41ff7ff48582850 0xfc83feffe90b050a 0xebfefb9e1878787e 0xfd7fdf73c30f0f0f

def z310 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0xe178839e1870787c 0x5c2f1073c30e0f0f

def z311 : W := mkw 0xac1fc3f61dd87d50 0xb583f87ec3bb0faa 0x013e839c1f707800 0x4027d07383ee0f00

def z312 : W := mkw 0x09000000b582d7ac 0x0120000016b05af5 0x004000001f8fffff 0xe008000003f1ffff

def z313 : W := mkw 0x0000080002240000 0x0000010000448000 0x1406380007060001 0x0280c70000e0c000

def z314 : W := mkw 0xc00af7fb40000000 0xf8015eff68000000 0xf800ffffe0000000 0x1f001ffffc000000

def z315 : W := mkw 0xf11ffffbfeef82ac 0xfe23ffff7fddf055 0xffffffffffff87ff 0xfffffffffffff0ff

def z316 : W := mkw 0xc81ff7fb41005500 0xf903feff68200aa0 0xffdfffffe0007f84 0x1ffbfffffc000ff0

def z317 : W := mkw 0xac1fc3f61dd87d50 0xb583f87ec3bb0faa 0xebfec39e1f78787e 0xfd7fd873c3ef0f0f

def z318 : W := mkw 0x0000000000000000 0x0000000000000000 0x4258018018001800 0x884b003003000300

def z319 : W := mkw 0xe41de5b648582850 0xdc83bcb6c90b050a 0xebf9c7be7878787e 0xfd7f38f7cf0f0f0f

def z320 : W := mkw 0x0100000020008088 0x0020000004001011 0x0001042060818180 0x000020840c103030

def z321 : W := mkw 0x3008ec000a6d0000 0xc6011d80014da000 0x1ea1fc0000ff8003 0xa3d43f80001ff000

def z322 : W := mkw 0x0002024001004400 0x2000404800200880 0x2000024000006604 0x0400004800000cc0

def z323 : W := mkw 0xa40ad2df08582850 0xb4815a5be10b050a 0xfffefbdf9878787e 0xffffdf7bf30f0f0f

def z324 : W := mkw 0x10152c0016a50000 0x4202a58002d4a000 0x1e877c00078f8003 0xa3d0ef8000f1f000

def z325 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xffdffffff8007804 0xfffbffffff000f00

def z326 : W := mkw 0x1000080016a50000 0x0200010002d4a000 0x0000000007878001 0x0000000000f0f000

def z327 : W := mkw 0xb41de4961cd92850 0xd683bc92c39b250a 0xebf9c79e18f9f87e 0xfd7f38f3c31f3f0f

def z328 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xff9fffffe08f8003 0xbff3fffffc11f000

def z329 : W := mkw 0xf01ffffb5eed0000 0xfe03ffff6bdda000 0x1fbfff9c1fff8003 0xe3f7fff383fff000

def z330 : W := mkw 0x01000000a00282ac 0x0020000014005055 0xbc810461e08787e7 0x3790208c3c10f0fc

def z331 : W := mkw 0x881fc3f215805500 0xb103f87e42b00aa0 0xefdfc3fe1f807f85 0xfdfbf87fc3f00ff0

def z332 : W := mkw 0x0320180da236a2ee 0x00640301b446d45d 0x9820fc1fe07f807a 0x13041f83fc0ff00f

def z333 : W := mkw 0x0000000000000000 0x0000000000000000 0x0040000000800785 0xa0080000001000f0

def z334 : W := mkw 0xac1dc1b61cd83950 0x9583b836c39b072a 0xebf9c3be18f879fe 0xfd7f3877c31f0f3f

def z335 : W := mkw 0xc22213ffc1126666 0x3844427ff8224ccc 0xe00003ffe0006664 0x1c00007ffc000ccc

def z336 : W := mkw 0x0000000000000000 0x0000000000000000 0xfec14402008f807f 0xbfd828804011f00f

def z337 : W := mkw 0x0017036000000000 0x2002e06c00000000 0x67df03e018007804 0xecfbe07c03000f00

def z338 : W := mkw 0x0000000400102040 0x0000000080020408 0x0120821c00706000 0x40241043800e0c00

def z339 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0x679fbbfc00000000 0x0cf3f77f80000000

def z340 : W := mkw 0x301fee401fed4400 0xe603fdc803fda880 0x3fbffe401fffe607 0xe7f7ffc803fffcc0

def z341 : W := mkw 0x0222124d81126666 0x20444249b0224ccc 0xa586025d87006665 0x74b0c04bb0e00ccc

def z342 : W := mkw 0x300008000a6d0000 0x06000100014da000 0x00200000007f8002 0x00040000000ff000

def z343 : W := mkw 0xa508c0962858a8d8 0x94a11812c50b151b 0xebf9c7be78f9f9fe 0xfd7f38f7cf1f3f3f

def z344 : W := mkw 0x02221a4903244402 0x2044434920648880 0x0006380007000000 0x0000c70000e00000

def z345 : W := mkw 0x0015000014800000 0x0002a00002900000 0x67df00601f800785 0xecfbe00c03f000f0

def z346 : W := mkw 0xc11ff7fbe00282ac 0xf823feff7c005055 0xffdfffffe00007fc 0x1ffbfffffc0000ff

def z347 : W := mkw 0x3008e40008490000 0xc6011c8001092000 0x0000440000098000 0x0000088000013000

def z348 : W := mkw 0xc01713fb40000000 0x3802e27f68000000 0xe79f03ffe0000000 0x1cf3e07ffc000000

def z349 : W := mkw 0x10002c0002250000 0x420005800044a000 0x10003c0000078000 0x020007800000f000

def z350 : W := mkw 0x2400000008480810 0x0480000001090102 0x0040000018081818 0x8008000003010303

def z351 : W := mkw 0x311dec00beef82ac 0xc623bd8017ddf055 0x9fbffc03ffff807b 0xf3f7ff807ffff00f

def z352 : W := mkw 0xb63ffedf9fff6e76 0xf6c7ffdbf3ffedce 0xffffffdf9ffffe7f 0xfffffffbf3ffffcf

def z353 : W := mkw 0x0015000014800000 0x0002a00002900000 0x0407000007800001 0x0080e00000f00000

def z354 : W := mkw 0xc11de5b260008088 0xd823bcb64c001011 0x425945a260898198 0x884b28b44c113033

def z355 : W := mkw 0x0000000000000000 0x0000000000000000 0x004000000008007e 0xa00800000001000f

def z356 : W := mkw 0x09170360b582d7ac 0x2122e06c16b05af5 0xfec74463e78f87ff 0xbfd8e88c7cf1f0ff

def z357 : W := mkw 0x2008c00408582040 0x84011800810b0408 0xabb8c21c18786066 0xf5771843830f0c0c

def z358 : W := mkw 0x0000000000000000 0x0000000000000000 0xbc80004180000000 0x1790000830000000

def z359 : W := mkw 0xae3fdbff9ffe7f76 0xb5c7fb7ff3ffcfee 0xfffffbff9ffe7fff 0xffffff7ff3ffcfff

def z360 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x1fbffc001f700000 0x43f7ff8003ee0000

def z361 : W := mkw 0xc81ff7fb54801100 0xf903feff6a900220 0xffdffffff8801980 0x9ffbffffff100330

def z362 : W := mkw 0xc22afedfc3366666 0xf8455fdbf866cccc 0xbda6fe5fe7766667 0x77b4dfcbfceecccc

def z363 : W := mkw 0x0000000000000000 0x0000000000000000 0xfec14463e008007e 0xbfd8288c7c01000f

def z364 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xb4063a5d87066665 0x1680c74bb0e0cccc

def z365 : W := mkw 0xa400009608582850 0x14800012c10b050a 0xe060039e1878787e 0xfc0c0073c30f0f0f

def z366 : W := mkw 0xa72adadfab7eeefe 0xb4e55b5bf56fdddf 0xffffffffffffffff 0xffffffffffffffff

def z367 : W := mkw 0x8400009600102850 0x10800012c002050a 0x8000001e00000078 0x10000003c000000f

def z368 : W := mkw 0x09170360b582d7ac 0x2122e06c16b05af5 0x14070461e7878781 0x0280e08c3cf0f0f0

def z369 : W := mkw 0xa508c096a85aaafc 0x94a11812d50b555f 0xfbf8c79ff87ff87e 0xff7f18f3ff0fff0f

def z370 : W := mkw 0x01000000a00282ac 0x0020000014005055 0xda414423e08f81fa 0x9b4828847c11f03f

def z371 : W := mkw 0xb41dec961efd2850 0xd683bd92c3dfa50a 0x9fbffc1e1fff807b 0xf3f7ff83c3fff00f

def z372 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x679f03e007800781 0x0cf3e07c00f000f0

def z373 : W := mkw 0x301de4001cc90000 0xc603bc8003992000 0x0bb9c40018f98002 0xe1773880031f3000

def z374 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0x9c07fc7fe0000000 0x1380ff8ffc000000

def z375 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x7ffffc601fff8787 0xefffff8c03fff0f0

def z376 : W := mkw 0x8008c09200000000 0x9001181240000000 0xff99c7ffe0000000 0x1ff338fffc000000

def z377 : W := mkw 0x381ded201eed1100 0xc703bda403dda220 0x5ffffda01fff9983 0xebffffb403fff330

def z378 : W := mkw 0x0800012000001100 0x0100002400000220 0x404001a000001980 0x0808003400000330

def z379 : W := mkw 0x01000000a00282ac 0x0020000014005055 0xfac04403e00f807e 0xbf5808807c01f00f

def z380 : W := mkw 0x0220180982260226 0x004403013044c044 0x1000380180060000 0x020007003000c000

def z381 : W := mkw 0x381de5201cc91100 0xc703bca403992220 0x425945a018899980 0x884b28b403113330

def z382 : W := mkw 0x201dc0001cc80000 0x8403b80003990000 0x0fbfc0001ff80003 0xe1f7f80003ff0000

def z383 : W := mkw 0x0000000000000000 0x0000000000000000 0x7ec14460008f8787 0xafd8288c0011f0f0

def z384 : W := mkw 0x86221adf83366e76 0x30c4435bf066cdce 0xfde6bbdf87767e7f 0x7fbcd77bf0eecfcf

def z385 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0x8938c39e1878787a 0x51271873c30f0f0f

def z386 : W := mkw 0x0000000000000000 0x0000000000000000 0x6681006000000000 0x0cd0200c00000000

def z387 : W := mkw 0x0a37136d95927766 0x2146e26db2b24eec 0xe7df03fd9f807fe5 0xfcfbe07fb3f00ffc

def z388 : W := mkw 0xf41fffff5efd2850 0xfe83ffffebdfa50a 0xfffffffffffff87f 0xffffffffffffff0f

def z389 : W := mkw 0x0000080002240000 0x0000010000448000 0x0126b80007700000 0x4024d70000ee0000

def z390 : W := mkw 0xbc1feff61ffd7d50 0xf783fdfec3ffafaa 0xfffffffe1fffffff 0xffffffffc3ffffff

def z391 : W := mkw 0x0015240000000000 0x4002a48000000000 0x14073c0000000000 0x0280e78000000000

def z392 : W := mkw 0x0002024001004400 0x2000404800200880 0x0106020007006000 0x4020c04000e00c00

def z393 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x015e03801f807f85 0xe02bc07003f00ff0

def z394 : W := mkw 0xe40ad3ff48582850 0xbc815a7fe90b050a 0xebf8c3fff878787e 0xfd7f187fff0f0f0f

def z395 : W := mkw 0x0000000000000000 0x0000000000000000 0x0201440000898000 0x8040288000113000

def z396 : W := mkw 0xa408c09208480810 0x9481181241090102 0xead841821808187e 0xbd5b08304301030f

def z397 : W := mkw 0x0000080082260224 0x000001001044c044 0xbda6b84187760667 0x77b4d70830eec0cc

def z398 : W := mkw 0x18172f6017a55500 0x6302e5ec02f4aaa0 0x14073c6007878781 0x0280e78c00f0f0f0

def z399 : W := mkw 0x0000000000000000 0x0000000000000000 0x1c80000000060003 0x239000000000c000

def z400 : W := mkw 0x091703603580d588 0x2122e06c06b01ab1 0x67df47e27f89ff9d 0xecfbe8fc4ff13ff3

def z401 : W := mkw 0x0002124900000000 0x2000424920000000 0x0106ba1c00000000 0x0020d74380000000

def z402 : W := mkw 0x0220180d82362266 0x00440301b046c44c 0xbca0b85d80760667 0x3794170bb00ec0cc

def z403 : W := mkw 0x311dec00beef82ac 0xc623bd8017ddf055 0x1fbffc61ffff8783 0xe3f7ff8c3ffff0f0

def z404 : W := mkw 0x0000000000000000 0x0000000000000000 0x2180020000006004 0x6430004000000c00

def z405 : W := mkw 0x0400000400102850 0x008000008002050a 0x004000000000787c 0x0008000000000f0f

def z406 : W := mkw 0x201de40008480000 0xc403bc8001090000 0x1fbffc0018780002 0xe3f7ff80030f0000

def z407 : W := mkw 0x0002124980020224 0x2000424930004044 0xbd86ba5d80060667 0x37b0d74bb000c0cc

def z408 : W := mkw 0x0817036415907540 0x2102e06c82b20ea8 0xefff83fc1ff07fe7 0xfdfff07f83fe0ffc

def z409 : W := mkw 0xac0ac3f609587d50 0xb581587ec12b0faa 0xebf8c3fe18787ffe 0xfd7f187fc30f0fff

def z410 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x1c27fc0007ff8003 0x0384ff8000fff000

def z411 : W := mkw 0x0000000000000000 0x0000000000000000 0xeec14062008807ff 0xbdd8280c401100ff

def z412 : W := mkw 0x0000000000000000 0x0000000000000000 0xebd843821808787e 0xfd7b087043010f0f

def z413 : W := mkw 0xe51ff7ffe85aaafc 0xfca3fefffd0b555f 0xfffffffff8ffffff 0xffffffffff1fffff

def z414 : W := mkw 0x02221a4d03346442 0x20444349a0668c88 0xa9a6ba1c07706066 0x7534d74380ee0c0c

def z415 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0x63f8839c18707804 0xec7f1073830e0f00

def z416 : W := mkw 0x09170360b582d7ac 0x2122e06c16b05af5 0x67df03e01f8fffff 0xecfbe07c03f1ffff

def z417 : W := mkw 0x301ffe491eed0000 0xe603ffc923dda000 0xbfbffe5d9fff8003 0xf7f7ffcbb3fff000

def z418 : W := mkw 0xc11ff7fbe00282ac 0xf823feff7c005055 0xff9fffffe00f807a 0x1ff3fffffc01f00f

def z419 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x63de03801f007804 0xec7bc07003e00f00

def z420 : W := mkw 0x0220180d82362266 0x00440301b046c44c 0xb9a0ba1d80766066 0x77341743b00ecc0c

def z421 : W := mkw 0x02221a4d03346442 0x20444349a0668c88 0x25a6ba5c07706605 0x64b4d74b80ee0cc0

def z422 : W := mkw 0x09020360a102d7ac 0x2120406c14205af5 0xfec147e3e08fffff 0xbfd828fc7c11ffff

def z423 : W := mkw 0x8400009600102850 0x10800012c002050a 0xeac0439e0008787e 0xbd580873c0010f0f

def z424 : W := mkw 0x41173769e00282ac 0x6822e6ed3c005055 0x14073c61e0878781 0x0280e78c3c10f0f0

def z425 : W := mkw 0xc008e49240000000 0xd8011c9248000000 0x0000440260000000 0x000008804c000000

def z426 : W := mkw 0x0017036001004400 0x2002e06c00200880 0x679f03e007006605 0x6cf3e07c00e00cc0

def z427 : W := mkw 0xc108f49be00282ac 0xd8211e937c005055 0xfec1fc7fe08f87ff 0xbfd83f8ffc11f0ff

def z428 : W := mkw 0x4817376955805500 0x6902e6ed2ab00aa0 0x77df3fe1ff807f85 0xeefbe7fc3ff00ff0

def z429 : W := mkw 0x0000080002240000 0x0000010000448000 0x1820b80000760002 0x03041700000ec000

def z430 : W := mkw 0x01000000a00282ac 0x0020000014005055 0x10000401e0078000 0x020000803c00f000

def z431 : W := mkw 0x301508001eed0000 0x0602a10003dda000 0x07bf00001fff8003 0xe0f7e00003fff000

def z432 : W := mkw 0x3a3fff6d9fff7766 0xe747ffedb3ffeeec 0xfffffffd9fffffe7 0xffffffffb3fffffc

def z433 : W := mkw 0x301de4001cc90000 0xc603bc8003992000 0x079f44001f898001 0xe0f3e88003f13000

def z434 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x044700601f807f85 0xe088e00c03f00ff0

def z435 : W := mkw 0x301dec009eef0224 0xc603bd8013dde044 0xbfbffc419fff8667 0xf7f7ff8833fff0cc

def z436 : W := mkw 0x001dec0002240000 0xc003bd8000448000 0x1fbffc0007760003 0x63f7ff8000eec000

def z437 : W := mkw 0x3108ec00aa6f82ac 0xc6211d80154df055 0xfee1fc63e0ff87ff 0xbfdc3f8c7c1ff0ff

def z438 : W := mkw 0x10152c0016a50000 0x4202a58002d4a000 0x179f3c001f878001 0xe2f3e78003f0f000

def z439 : W := mkw 0x01000000a00282ac 0x0020000014005055 0xe2414463e08987fc 0x9c48288c7c1130ff

def z440 : W := mkw 0xb408c8961efd2850 0x96811912c3dfa50a 0xebf8c39e1ffff87f 0xfd7f1873c3ffff0f

def z441 : W := mkw 0xc108f49be00282ac 0xd8211e937c005055 0x9800fc1fe00f807a 0x13001f83fc01f00f

def z442 : W := mkw 0x01000000a00282ac 0x0020000014005055 0xfcc00063e00607ff 0x3f98000c7c00c0ff

def z443 : W := mkw 0xc23fffff43346442 0xf847ffffe8668c88 0xffbfffffe7706000 0x5ff7fffffcee0c00

def z444 : W := mkw 0x42373f69c3264626 0x6846e7ed3864c8c4 0x14073c61e7060601 0x0280e78c3ce0c0c0

def z445 : W := mkw 0x2400000408582850 0x04800000810b050a 0x002000000078007a 0x00040000000f000f

def z446 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0xefdf43e21f887fff 0xfdfbe87c43f10fff

def z447 : W := mkw 0x381fef601fed5500 0xe703fdec03fdaaa0 0x013ebb801f707800 0x4027d77003ee0f00

def z448 : W := mkw 0x8008c09200000000 0x9001181240000000 0x0118839c00000000 0x0023107380000000

def z449 : W := mkw 0x01000000a00282ac 0x0020000014005055 0x98404403e08f87ff 0xb30808807c11f0ff

def z450 : W := mkw 0x01000000a00282ac 0x0020000014005055 0x80000003e0000078 0x100000007c00000f

def z451 : W := mkw 0x862212df81126e76 0x30c4425bf0224dce 0xe04003df80007e7c 0x1c08007bf0000fcf

def z452 : W := mkw 0x02221a4983264626 0x204443493064c8c4 0x35863a4187066605 0x66b0c74830e0ccc0

def z453 : W := mkw 0x391fef60bfefd7ac 0xe723fdec17fdfaf5 0xffffffe3ffffffff 0xfffffffc7fffffff

def z454 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xffdfffffe008007e 0xbffbfffffc01000f

def z455 : W := mkw 0xe41ff7ff48582850 0xfc83feffe90b050a 0xffbffffff8707800 0x5ff7ffffff0e0f00

def z456 : W := mkw 0x301de4001cc90000 0xc603bc8003992000 0x1f9ffc0018898000 0x83f3ff8003113000

def z457 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x079f00601f800781 0xe0f3e00c03f000f0

def z458 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x051f03e01f807f81 0x40a3e07c03f00ff0

def z459 : W := mkw 0x8108c092a00282ac 0x9021181254005055 0xffd9c7ffe08f87ff 0xbffb38fffc11f0ff

def z460 : W := mkw 0x0000000000000000 0x0000000000000000 0x2480004000000605 0x24900008000000c0

def z461 : W := mkw 0x0017036000000000 0x2002e06c00000000 0x011e038000000000 0x0023c07000000000

def z462 : W := mkw 0x0000000400102040 0x0000000080020408 0x0020000000706066 0x60040000000e0c0c

def z463 : W := mkw 0x0322124da112e6ee 0x20644249b4225cdd 0xfec1467fe08fe7ff 0xbfd828cffc11fcff

def z464 : W := mkw 0x0000000014800000 0x0000000002900000 0x000000001f800001 0xe000000003f00000

def z465 : W := mkw 0x4817376955805500 0x6902e6ed2ab00aa0 0x14073c61e7800781 0x0280e78c3cf000f0

def z466 : W := mkw 0x8000009200000000 0x1000001240000000 0xe000039e00000000 0x1c000073c0000000

def z467 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x033ffc001ff98000 0xc067ff8003ff3000

def z468 : W := mkw 0x0000000000000000 0x0000000000000000 0xa880000000000066 0x351000000000000c

def z469 : W := mkw 0x0220080403346442 0x0044010080668c88 0x0020000007706000 0x4004000000ee0c00

def z470 : W := mkw 0xc91ff7fbf582d7ac 0xf923feff7eb05af5 0xffdfffffff8fffff 0xfffbfffffff1ffff

def z471 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x153fbc001ff78001 0x42a7f78003fef000

def z472 : W := mkw 0x8008c09600102040 0x90011812c0020408 0xebb8c39e00706066 0x7d771873c00e0c0c

def z473 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x7fffff801ffff807 0xeffffff003ffff00

def z474 : W := mkw 0xa62adadf8b7e6e76 0xb4c55b5bf16fcdce 0xbda6fa5f877e667f 0x77b4df4bf0efcccf

def z475 : W := mkw 0x311de4003cc98088 0xc623bc8007993011 0x4259442278898198 0x884b28844f113033

def z476 : W := mkw 0x01000000a00282ac 0x0020000014005055 0x0000000000878781 0x000000000010f0f0

def z477 : W := mkw 0xac1fc3f61dd87d50 0xb583f87ec3bb0faa 0x67ff83fc1ff07f85 0xecfff07f83fe0ff0

def z478 : W := mkw 0x0015080016a40000 0x0002a10002d48000 0x1fbfb8001ff60003 0xe3f7f70003fec000

def z479 : W := mkw 0x8c0203f601107d50 0x3180407ec0220faa 0xe04003fe00007ffc 0x1c08007fc0000fff

def z480 : W := mkw 0xa508c096a85aaafc 0x94a11812d50b555f 0xfee1c47fe0ff87ff 0xbfdc388ffc1ff0ff

def z481 : W := mkw 0x0002024001004400 0x2000404800200880 0x67c7026007806785 0xecf8e04c00f00cf0

def z482 : W := mkw 0x01000000a00282ac 0x0020000014005055 0x42414422608f87ff 0xa84828844c11f0ff

def z483 : W := mkw 0x0000000400102040 0x0000000080020408 0xebe0c21e0078607e 0xfd7c1843c00f0c0f

def z484 : W := mkw 0x0802024015805500 0x2100404802b00aa0 0x25c602401f807f85 0xe4b8c04803f00ff0

def z485 : W := mkw 0x380008001fed5500 0x0700010003fdaaa0 0x006000001fffff87 0xe00c000003fffff0

def z486 : W := mkw 0x01000000a00282ac 0x0020000014005055 0xfe814463e0878781 0x1fd0288c7c10f0f0

def z487 : W := mkw 0x3008ec000a6d0000 0xc6011d80014da000 0x0020b80000700000 0x00041700000e0000

def z488 : W := mkw 0xa408c09208480810 0x9481181241090102 0x0000400200080018 0x0000080040010003

def z489 : W := mkw 0x4000340940000000 0x4800068128000000 0x10003c01e0000000 0x020007803c000000

def z490 : W := mkw 0x0222124d01106442 0x20444249a0220c88 0x0000021c00006000 0x0000004380000c00

def z491 : W := mkw 0xc00213fb40000000 0x3800427f68000000 0xfd86bbffe0000000 0x1fb0d77ffc000000

def z492 : W := mkw 0x1015240014810000 0x4202a48002902000 0x0001040000818000 0x0000208000103000

def z493 : W := mkw 0x0000000000000000 0x0000000000000000 0x6040038000007804 0x0c08007000000f00

def z494 : W := mkw 0x11152c00b6a782ac 0x4222a58016d4f055 0xfec77c63e78f87ff 0xbfd8ef8c7cf1f0ff

def z495 : W := mkw 0xa008c09208480000 0x9401181241090000 0xebb8c39e18780002 0xfd771873c30f0000

def z496 : W := mkw 0xc40213ff40102850 0x3880427fe802050a 0xe04003ffe000787c 0x1c08007ffc000f0f

def z497 : W := mkw 0x01000000a00282ac 0x0020000014005055 0x00000000000f807a 0x000000000001f00f

def z498 : W := mkw 0x023ffe4d83366666 0xe047ffc9b066cccc 0xbfbffe5d87766667 0x77f7ffcbb0eecccc

def z499 : W := mkw 0x301de4001cc90000 0xc603bc8003992000 0x0018000018000000 0x0003000003000000

def z500 : W := mkw 0x0017136900000000 0x2002e26d20000000 0xff9fbbfd80000000 0x1ff3f77fb0000000

def z501 : W := mkw 0x801de49200000000 0xd003bc9240000000 0xff9fff9e00000000 0x1ff3fff3c0000000

def z502 : W := mkw 0x01000000a00282ac 0x0020000014005055 0x1ec14400008f87ff 0xa3d828800011f0ff

def z503 : W := mkw 0x01000000a00282ac 0x0020000014005055 0x00000061e0000780 0x0000000c3c0000f0

def z504 : W := mkw 0x323dfc0d9eff2266 0xc647bf81b3dfe44c 0x9fbffc1d9fff8063 0xf3f7ff83b3fff00c

def z505 : W := mkw 0x01000000a00282ac 0x0020000014005055 0xfe814463e00f807a 0x1fd0288c7c01f00f

def z506 : W := mkw 0xb51dec96beffaafc 0xd6a3bd92d7dff55f 0xffffffffffffffff 0xffffffffffffffff

def z507 : W := mkw 0x11152c00b6a782ac 0x4222a58016d4f055 0x14073c61e7878781 0x0280e78c3cf0f0f0

def z508 : W := mkw 0x0002124901004400 0x2000424920200880 0xbd86ba5d87006605 0x77b0d74bb0e00cc0

def z509 : W := mkw 0x8400009200000810 0x1080001240000102 0x4040018200001818 0x0808003040000303

def z510 : W := mkw 0x0220000481126666 0x0044000090224ccc 0x0000000000006664 0x0000000000000ccc

def z511 : W := mkw 0x0000000000000000 0x0000000000000000 0xe0000063e0000000 0x1c00000c7c000000

def z512 : W := mkw 0x323ffe4d1ffd6442 0xe647ffc9a3ffac88 0x013eba1c1f706000 0x4027d74383ee0c00

def z513 : W := mkw 0xc81ff7fb55805500 0xf903feff6ab00aa0 0xff9fffffff007800 0x5ff3ffffffe00f00

def z514 : W := mkw 0x8400009600102850 0x10800012c002050a 0x0000039c00007800 0x0000007380000f00

def z515 : W := mkw 0x0000000000000000 0x0000000000000000 0xfec14463e0800785 0xbfd8288c7c1000f0

def z516 : W := mkw 0x381dec001fed5500 0xc703bd8003fdaaa0 0x1ffffc001fffff87 0xe3ffff8003fffff0

def z517 : W := mkw 0x8408c09600102850 0x90811812c002050a 0xebd8c39e0000787c 0x1d7b1873c0000f0f

def z518 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xeb9efb9e00000000 0x1d73df73c0000000

def z519 : W := mkw 0x0000000080020224 0x0000000010004044 0xfec04043800e067f 0xbfd808087001c0cf

def z520 : W := mkw 0x0802036015805500 0x2100406c02b00aa0 0x604003e01f807f85 0xec08007c03f00ff0

def z521 : W := mkw 0x0000000400102040 0x0000000080020408 0xa000021c00006064 0x1400004380000c0c

def z522 : W := mkw 0x333ffe4dbfffe6ee 0xe667ffc9b7fffcdd 0xfffffe7fffffe7ff 0xffffffcffffffcff

def z523 : W := mkw 0xc11de5b2e00282ac 0xd823bcb65c005055 0xfed945e3e08f87ff 0xbfdb28bc7c11f0ff

def z524 : W := mkw 0x0222124981024626 0x20444249302048c4 0x0000004180000600 0x00000008300000c0

def z525 : W := mkw 0x85000096a012aafc 0x10a00012d402555f 0xfec147ffe08fffff 0xbfd828fffc11ffff

def z526 : W := mkw 0xb41dec961efd2850 0xd683bd92c3dfa50a 0x1fbfff9c1ffff803 0xe3f7fff383ffff00

def z527 : W := mkw 0xf01ffffb5eed0000 0xfe03ffff6bdda000 0xffbfffffff700000 0x5ff7ffffffee0000

def z528 : W := mkw 0xc00ad3fb40000000 0xb8015a7f68000000 0xeb98c3ffe0000000 0x1d73187ffc000000

def z529 : W := mkw 0xa408c09208480810 0x9481181241090102 0x4bf8c1821878181a 0xe97f1830430f0303

def z530 : W := mkw 0x0000000000000000 0x0000000000000000 0xa980821c00000000 0x1530104380000000

def z531 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0x561f7de3e0000000 0x0ac3efbc7c000000

def z532 : W := mkw 0xa408c09208480810 0x9481181241090102 0xebd8c39e18081818 0x9d7b1873c3010303

def z533 : W := mkw 0x0000000480122264 0x000000009002444c 0xbda0825d80766667 0x77b4104bb00ecccc

def z534 : W := mkw 0x0000000000000000 0x0000000000000000 0x0586000007000001 0x60b0c00000e00000

def z535 : W := mkw 0x0a371b6d97b67766 0x2146e36db2f6ceec 0xbda7ba7d87f667e7 0x77b4f74fb0feccfc

def z536 : W := mkw 0x0017024015804400 0x2002e04802b00880 0x279f02401f806605 0xe4f3e04803f00cc0

def z537 : W := mkw 0xa62ad2df895a6e76 0xb4c55a5bf12b4dce 0xebf8c3df98787e7e 0xfd7f187bf30f0fcf

def z538 : W := mkw 0x01000000a00282ac 0x0020000014005055 0x56414463e08f8799 0x8ac8288c7c11f0f3

def z539 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x0bbef8001f780002 0xe177df0003ef0000

def z540 : W := mkw 0x32221a4d9fff6666 0x26444349b3ffeccc 0xbda6ba5d9fffe667 0xf7b4d74bb3fffccc

def z541 : W := mkw 0xc23fffffc3366666 0xf847fffff866cccc 0xbdbebbdd87766667 0x77b7d77bb0eecccc

def z542 : W := mkw 0x0008e40000000000 0xc0011c8000000000 0x1800fc0000000000 0x03001f8000000000

def z543 : W := mkw 0x01170360a00282ac 0x2022e06c14005055 0xffdf47e3e08f87ff 0xbffbe8fc7c11f0ff

def z544 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x465f01e01f801f81 0x88cbe03c03f003f0

def z545 : W := mkw 0xc23fffff43346442 0xf847ffffe8668c88 0x013ebb9c07706000 0x4027d77380ee0c00

def z546 : W := mkw 0x0000000000000000 0x0000000000000000 0x1401040000878001 0x028020800010f000

def z547 : W := mkw 0x2400000408582850 0x04800000810b050a 0xa9e0821c1878787e 0xf53c1043830f0f0f

def z548 : W := mkw 0x0222124d81126666 0x20444249b0224ccc 0xa9a0825d80706666 0x7534104bb00e0ccc

def z549 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x079f03801f807801 0xe0f3e07003f00f00

def z550 : W := mkw 0xa408c8960a7c2850 0x94811912c14f850a 0xfffefb9e1f7e787f 0xffffdf73c3efcf0f

def z551 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0x8bb8c01e1878007a 0xf1771803c30f000f

def z552 : W := mkw 0x322afe4d8b7f6666 0xe6455fc9b16feccc 0xbda6fe5d877fe667 0x77b4dfcbb0effccc

def z553 : W := mkw 0x0100000020008088 0x0020000004001011 0x0000440260098018 0x000008804c013003

def z554 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x07bfb8001ff00001 0xe0f7f70003fe0000

def z555 : W := mkw 0xc008f49b40000000 0xd8011e9368000000 0x0000b81c00000000 0x0000170380000000

def z556 : W := mkw 0xc000109b40000000 0x1800021368000000 0x8000001fe0000000 0x10000003fc000000

def z557 : W := mkw 0x0220080483366666 0x004401009066cccc 0xa9a0821c07766667 0x7534104380eecccc

def z558 : W := mkw 0x311dec003eed8088 0xc623bd8007ddb011 0x5ffffc227fff819b 0xebffff844ffff033

def z559 : W := mkw 0x01000000a00282ac 0x0020000014005055 0xbc804443e00f867f 0x379008887c01f0cf

def z560 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x625903e018807f84 0x8c4b207c03100ff0

def z561 : W := mkw 0x001ff64900000000 0xe003fec920000000 0xbf9ffe5d80000000 0x17f3ffcbb0000000

def z562 : W := mkw 0x38170b601fed5500 0x2702e16c03fdaaa0 0x67ff03e01fffff87 0xecffe07c03fffff0

def z563 : W := mkw 0x0220080482362266 0x004401009046c44c 0x0020000000760062 0x00040000000ec00c

def z564 : W := mkw 0x09150120b48293ac 0x0122a02416905275 0xfed945e3f88f9fff 0xbfdb28bc7f11f3ff

def z565 : W := mkw 0xa628d89f8a7e2a76 0x94c51b13f14fc54e 0x9820f81f807e007a 0x13041f03f00fc00f

def z566 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xb820ba5d80766666 0x1704174bb00ecccc

def z567 : W := mkw 0x4017376940000000 0x6802e6ed28000000 0x779f3fe1e0000000 0x0ef3e7fc3c000000

def z568 : W := mkw 0x8c1703f615907d50 0x3182e07ec2b20faa 0xe7df03fe1f807ffd 0xfcfbe07fc3f00fff

def z569 : W := mkw 0x0000000000000000 0x0000000000000000 0x14010461e0000000 0x0280208c3c000000

def z570 : W := mkw 0xc01ff7ff40102040 0xf803feffe8020408 0xffbfffffe0706066 0x7ff7fffffc0e0c0c

def z571 : W := mkw 0xa62adadf0b7c6c52 0xb4c55b5be16f8d8a 0x013ebb9c1f707800 0x4027d77383ee0f00

def z572 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000008f8003 0xa00000000011f000

def z573 : W := mkw 0xc10213fbe00282ac 0x3820427f7c005055 0xe04003ffe00007fc 0x1c08007ffc0000ff

def z574 : W := mkw 0x0000000400102040 0x0000000080020408 0x8820801c00700062 0x11041003800e000c

def z575 : W := mkw 0x101dec0016a50000 0xc203bd8002d4a000 0x1f9ffc0007878001 0x03f3ff8000f0f000

def z576 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x1dbeb8001f760003 0x63b7d70003eec000

def z577 : W := mkw 0x300008001eed0000 0x0600010003dda000 0x1ea144001fff8003 0xe3d4288003fff000

def z578 : W := mkw 0x0a371b6997a65726 0x2146e36d32f4cae4 0x77df3be19f867f85 0xeefbe77c33f0cff0

def z579 : W := mkw 0x0000000000000000 0x0000000000000000 0x0681000000800001 0xa0d0200000100000

def z580 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xe21947ffe0000000 0x1c4328fffc000000

def z581 : W := mkw 0x0817036014801100 0x2102e06c02900220 0x67df03e018801980 0x8cfbe07c03100330

def z582 : W := mkw 0x01000000a00282ac 0x0020000014005055 0xf4410463e08787fd 0x1e88208c7c10f0ff

def z583 : W := mkw 0xc00213fb40000000 0x3800427f68000000 0xfe8147ffe0000000 0x1fd028fffc000000

def z584 : W := mkw 0x0802036001005500 0x2100406c00200aa0 0x65c603e007007f85 0x6cb8c07c00e00ff0

def z585 : W := mkw 0x800ad2db00000000 0xb0015a5b60000000 0xff9efbdf80000000 0x1ff3df7bf0000000

def z586 : W := mkw 0xf01ffffb4a6d0000 0xfe03ffff694da000 0xffbfffffe07f8002 0x1ff7fffffc0ff000

def z587 : W := mkw 0xc2221bffc3366666 0x3844437ff866cccc 0xfda6bbffe7766667 0x7fb4d77ffceecccc

def z588 : W := mkw 0xc01de5b240000000 0xd803bcb648000000 0x5f9ffda260000000 0x0bf3ffb44c000000

def z589 : W := mkw 0x222ada4d8b7e6666 0xa4455b49b16fcccc 0xbfbefa5d9f7e6667 0xf7f7df4bb3efcccc

def z590 : W := mkw 0xc01de5b240000000 0xd803bcb648000000 0x0018018000000000 0x0003003000000000

def z591 : W := mkw 0x0100000020008088 0x0020000004001011 0x4040002260000198 0x080800044c000033

def z592 : W := mkw 0x8400009600102850 0x10800012c002050a 0xe3d8039e1800787c 0xfc7b0073c3000f0f

def z593 : W := mkw 0xb408ec960a7d2850 0xd6811d92c14fa50a 0x9820fc1e007f807a 0x13041f83c00ff00f

def z594 : W := mkw 0x01000004a012a2ec 0x002000009402545d 0xffe1c67fe0ffe7ff 0xfffc38cffc1ffcff

def z595 : W := mkw 0x301dec041efd2040 0xc603bd8083dfa408 0xbfbffe1c1fffe067 0xf7f7ffc383fffc0c

def z596 : W := mkw 0xa628c8968b7e6e76 0x94c51912d16fcdce 0xebf8c39e1f7e7e7f 0xfd7f1873c3efcfcf

def z597 : W := mkw 0x01000000a00282ac 0x0020000014005055 0x76c10461e0878785 0xaed8208c3c10f0f0

def z598 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x66c7006007800785 0xacd8e00c00f000f0

def z599 : W := mkw 0x340008041efd2850 0x0680010083dfa50a 0x006000001ffff87f 0xe00c000003ffff0f

def z600 : W := mkw 0xf008fc9b4a6d0000 0xde011f93694da000 0x9820fc1fe07f8002 0x13041f83fc0ff000

def z601 : W := mkw 0x02221a4983264626 0x204443493064c8c4 0xbc86384187060667 0x3790c70830e0c0cc

def z602 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0xffbffc63ffff8003 0xfff7ff8c7ffff000

def z603 : W := mkw 0x0000000000000000 0x0000000000000000 0x0401006000800781 0x0080200c001000f0

def z604 : W := mkw 0x0000000080020224 0x0000000010004044 0xa000004180000664 0x14000008300000cc

def z605 : W := mkw 0x0000000000000000 0x0000000000000000 0x0118038018007800 0x4023007003000f00

def z606 : W := mkw 0x001de40000000000 0xc003bc8000000000 0x011eb80000000000 0x0023d70000000000

def z607 : W := mkw 0x01000000a00282ac 0x0020000014005055 0xe6c10063e08007fd 0xbcd8200c7c1000ff

def z608 : W := mkw 0x42373f6dc3366666 0x6846e7edb866cccc 0xbda7be7de7766667 0x77b4f7cfbceecccc

def z609 : W := mkw 0x381fef601fed5500 0xe703fdec03fdaaa0 0x67ffbbe01ff07f85 0xecfff77c03fe0ff0

def z610 : W := mkw 0x0002024001004400 0x2000404800200880 0x67de03c01f007e05 0xecfbc07803e00fc0

def z611 : W := mkw 0xc23ffffbc3264626 0xf847ffff7864c8c4 0xff9fffffe7060601 0x1ff3fffffce0c0c0

def z612 : W := mkw 0x0017036000000000 0x2002e06c00000000 0x0407006000000000 0x0080e00c00000000

def z613 : W := mkw 0x001de40000000000 0xc003bc8000000000 0xff9ffc63e0000000 0x1ff3ff8c7c000000

def z614 : W := mkw 0x0017036000000000 0x2002e06c00000000 0xff9f47e3e0000000 0x1ff3e8fc7c000000

def z615 : W := mkw 0xa628d89f8a7e2a76 0x94c51b13f14fc54e 0xfbf8fb9f987e787e 0xff7f1f73f30fcf0f

def z616 : W := mkw 0xf01ffffb5eed0000 0xfe03ffff6bdda000 0x013ebb9c1f700000 0x4027d77383ee0000

def z617 : W := mkw 0xc80213fb41005500 0x3900427f68200aa0 0xe04003ffe0007f84 0x1c08007ffc000ff0

def z618 : W := mkw 0x0015000014800000 0x0002a00002900000 0x011e00001f000000 0x4023c00003e00000

def z619 : W := mkw 0x262008048b7e6e76 0x04c40100916fcdce 0x006000001f7e7e7f 0xe00c000003efcfcf

def z620 : W := mkw 0x0000000000000000 0x0000000000000000 0x09a0800000700002 0x61341000000e0000

def z621 : W := mkw 0x02220a4483366666 0x204441489066cccc 0x25a6024007766667 0x64b4c04800eecccc

def z622 : W := mkw 0x0802036001005500 0x2100406c00200aa0 0x66c103e000807f85 0xacd8207c00100ff0

def z623 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0xca78c19e1878187a 0x994f1833c30f030f

def z624 : W := mkw 0x01000000a00282ac 0x0020000014005055 0xbcc00041808f87ff 0xb79800083011f0ff

def z625 : W := mkw 0xf81ffffb5fed5500 0xff03ffff6bfdaaa0 0xffffffffffffff87 0xfffffffffffffff0

def z626 : W := mkw 0x341dec041efd2850 0xc683bd8083dfa50a 0x1ffffc001ffff87f 0xe3ffff8003ffff0f

def z627 : W := mkw 0x10152c0016a50000 0x4202a58002d4a000 0x0006380007000000 0x0000c70000e00000

def z628 : W := mkw 0x0000000000000000 0x0000000000000000 0x1d86b80000000000 0x03b0d70000000000

def z629 : W := mkw 0x31000800beef82ac 0x0620010017ddf055 0xfee14463ffff87ff 0xffdc288c7ffff0ff

def z630 : W := mkw 0x0817036001005500 0x2102e06c00200aa0 0x67df03e000007f84 0x0cfbe07c00000ff0

def z631 : W := mkw 0xa62adadf8b7e6e76 0xb4c55b5bf16fcdce 0xbdbebbdd9f767e67 0x77b7d77bb3eecfcc

def z632 : W := mkw 0xc01de5b240000000 0xd803bcb648000000 0xeb99c7be60000000 0x1d7338f7cc000000

def z633 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0xe258439e1808787c 0x9c4b0873c3010f0f

def z634 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0x427841821878787e 0xe84f0830430f0f0f

def z635 : W := mkw 0x09170360b582d7ac 0x2122e06c16b05af5 0xe7df03e3ff807ffd 0xfcfbe07c7ff00fff

def z636 : W := mkw 0x0000000080020224 0x0000000010004044 0x0000000000060667 0x200000000000c0cc

def z637 : W := mkw 0xb408ec960a7d2850 0xd6811d92c14fa50a 0xfbf8ff9e187ff87e 0xff7f1ff3c30fff0f

def z638 : W := mkw 0x0815012014801100 0x0102a02402900220 0x66d901e018801f85 0xacdb203c031003f0

def z639 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0x8860c01e1878787e 0xf10c1803c30f0f0f

def z640 : W := mkw 0x0000000080020224 0x0000000010004044 0xfe814463e0060667 0x3fd0288c7c00c0cc

def z641 : W := mkw 0x01000000a00282ac 0x0020000014005055 0x66c10060008f87ff 0xacd8200c0011f0ff

def z642 : W := mkw 0x0000000000000000 0x0000000000000000 0x4240400200080018 0x8848080040010003

def z643 : W := mkw 0x0000000000000000 0x0000000000000000 0x0040000018007804 0xe008000003000f00

def z644 : W := mkw 0xc00001b240000000 0x1800003648000000 0x400001a260000000 0x080000344c000000

def z645 : W := mkw 0x4002136940000000 0x2800426d28000000 0x00000061e0000000 0x0000000c3c000000

def z646 : W := mkw 0x0815000015805500 0x0102a00002b00aa0 0x07df00001f807f85 0xe0fbe00003f00ff0

def z647 : W := mkw 0x0802036001005500 0x2100406c00200aa0 0x0000038000007800 0x0000007000000f00

def z648 : W := mkw 0x3008ec001eed0000 0xc6011d8003dda000 0x1820fc001fff8003 0xe3041f8003fff000

def z649 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x679f03e01f007800 0x4cf3e07c03e00f00

def z650 : W := mkw 0xa508c096a85aaafc 0x94a11812d50b555f 0xebf8c3fff8787ffe 0xfd7f187fff0f0fff

def z651 : W := mkw 0x0815012014801100 0x0102a02402900220 0x0001002000800180 0x0000200400100030

def z652 : W := mkw 0xc81fe7f255805500 0xf903fcfe4ab00aa0 0x67df47e27f807f85 0xecfbe8fc4ff00ff0

def z653 : W := mkw 0xc23fffffc2362266 0xf847fffff846c44c 0xffbfffffe0760062 0x1ff7fffffc0ec00c

def z654 : W := mkw 0x801fc3f200000000 0xb003f87e40000000 0xef9fc3fe00000000 0x1df3f87fc0000000

def z655 : W := mkw 0x0800000015805500 0x0100000002b00aa0 0x0000000007800781 0x0000000000f000f0

def z656 : W := mkw 0x8400009600102850 0x10800012c002050a 0xe9e0839e0070787e 0x7d3c1073c00e0f0f

def z657 : W := mkw 0x2400000408582850 0x04800000810b050a 0xeae040021878787e 0xfd5c0800430f0f0f

def z658 : W := mkw 0xa41dc0961cd82850 0x9483b812c39b050a 0xefffc39e1ff8787f 0xfdfff873c3ff0f0f

def z659 : W := mkw 0x0015000014800000 0x0002a00002900000 0x67df03801f807805 0xecfbe07003f00f00

def z660 : W := mkw 0x0a371b6d97b67766 0x2146e36db2f6ceec 0xbdbebbdd9f767e67 0x77b7d77bb3eecfcc

def z661 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0x0bb8c39c18787802 0xe1771873830f0f00

def z662 : W := mkw 0x01000000a00282ac 0x0020000014005055 0x9e814403e08f807b 0xb3d028807c11f00f

def z663 : W := mkw 0x2408c00408582850 0x84811800810b050a 0x0bf8c0001878787e 0xe17f1800030f0f0f

def z664 : W := mkw 0x0220080083264626 0x004401001064c8c4 0x0000000007060601 0x0000000000e0c0c0

def z665 : W := mkw 0x09000000b582d7ac 0x0120000016b05af5 0xfec14463ff8fffff 0xffd8288c7ff1ffff

def z666 : W := mkw 0x323ffe499fef4626 0xe647ffc933fde8c4 0x1fbffc419fff8603 0xe3f7ff8833fff0c0

def z667 : W := mkw 0xc11ff7fb60008088 0xf823feff6c001011 0xffdfffffe0898198 0x9ffbfffffc113033

def z668 : W := mkw 0xa408c09208480810 0x9481181241090102 0x63d843821808781c 0xec7b087043010f03

def z669 : W := mkw 0xc228fc9fc2362266 0xd8451f93f846c44c 0x9820fc1fe0760062 0x13041f83fc0ec00c

def z670 : W := mkw 0x01150000b48282ac 0x0022a00016905055 0xffdf4463ff8f87ff 0xfffbe88c7ff1f0ff

def z671 : W := mkw 0x01000000a00282ac 0x0020000014005055 0x00400000000007fc 0x00080000000000ff

def z672 : W := mkw 0xe63fffffcb7e6e76 0xfcc7fffff96fcdce 0xffffffffff7e7e7f 0xffffffffffefcfcf

def z673 : W := mkw 0xac1fc3f21dc85d10 0xb583f87e43b90ba2 0x67df43e21f887f9d 0xecfbe87c43f10ff3

def z674 : W := mkw 0xb41dec961efd2850 0xd683bd92c3dfa50a 0x013ebb9c1f707800 0x4027d77383ee0f00

def z675 : W := mkw 0x0222124d81126666 0x20444249b0224ccc 0xbd86ba5d80006664 0x17b0d74bb0000ccc

def z676 : W := mkw 0x25000004a85aaafc 0x04a00000950b555f 0xfee14463f8ffffff 0xffdc288c7f1fffff

def z677 : W := mkw 0x31000800beef82ac 0x0620010017ddf055 0x006000001fff87ff 0xe00c000003fff0ff

def z678 : W := mkw 0x2008c00008480000 0x8401180001090000 0x1fb9c40018ff8003 0xe3f73880031ff000

def z679 : W := mkw 0x0002036000000000 0x2000406c00000000 0x600003e000000000 0x0c00007c00000000

def z680 : W := mkw 0x12373e4997a74626 0x6246e7c932f4e8c4 0x14073c4187878601 0x0280e78830f0f0c0

def z681 : W := mkw 0x381fe7601dc95500 0xe703fcec03b92aa0 0x67df47e01f89ff85 0xecfbe8fc03f13ff0

def z682 : W := mkw 0x2008c00008480000 0x8401180001090000 0x6bf8c38018787806 0xed7f1870030f0f00

def z683 : W := mkw 0x0000000000000000 0x0000000000000000 0xe04000020000007c 0x1c0800004000000f

def z684 : W := mkw 0x0000000080020224 0x0000000010004044 0x1400004180060601 0x028000083000c0c0

def z685 : W := mkw 0x381fef601fed5500 0xe703fdec03fdaaa0 0x1fbffc601fff8783 0xe3f7ff8c03fff0f0

def z686 : W := mkw 0xe41ff7ff48582850 0xfc83feffe90b050a 0x013ebb9c18707800 0x4027d773830e0f00

def z687 : W := mkw 0x0815012014801100 0x0102a02402900220 0x47df01a01f801981 0xe8fbe03403f00330

def z688 : W := mkw 0x0817036095825724 0x2102e06c12b04ae4 0xffdf03e19f867fe7 0xfffbe07c33f0cffc

def z689 : W := mkw 0x0000000080020224 0x0000000010004044 0x9800000180060062 0x130000003000c00c

def z690 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x2587026007806785 0x64b0e04c00f00cf0

def z691 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0xeae0c01e0078007e 0xbd5c1803c00f000f

def z692 : W := mkw 0x00020a4003244400 0x2000414800648880 0x3da6ba4007766607 0x67b4d74800eeccc0

def z693 : W := mkw 0x0002024000000000 0x2000404800000000 0x2586024000000000 0x04b0c04800000000

def z694 : W := mkw 0x0220080483366666 0x004401009066cccc 0x1da6b80007766667 0x63b4d70000eecccc

def z695 : W := mkw 0xad1fc3f6bddafffc 0xb5a3f87ed7bb5fff 0xffffc7ffffffffff 0xfffff8ffffffffff

def z696 : W := mkw 0x09020360a102d7ac 0x2120406c14205af5 0xe04003e3e0007ffc 0x1c08007c7c000fff

def z697 : W := mkw 0x03221a49a326c6ae 0x206443493464d8d5 0xfec77c63e78f87ff 0xbfd8ef8c7cf1f0ff

def z698 : W := mkw 0x300008001eed0000 0x0600010003dda000 0x002000001f700000 0x4004000003ee0000

def z699 : W := mkw 0x0802036001005500 0x2100406c00200aa0 0x0000006000000780 0x0000000c000000f0

def z700 : W := mkw 0x4015252040000000 0x4802a4a408000000 0x0001042060000000 0x000020840c000000

def z701 : W := mkw 0xc81713fb55805500 0x3902e27f6ab00aa0 0xe7df03ffff807f85 0xfcfbe07ffff00ff0

def z702 : W := mkw 0x02221a4983264626 0x204443493064c8c4 0xbd86ba5d87060601 0x17b0d74bb0e0c0c0

def z703 : W := mkw 0x01000000a00282ac 0x0020000014005055 0x1e814461e08f8783 0xa3d0288c3c11f0f0

def z704 : W := mkw 0x311dec00beef82ac 0xc623bd8017ddf055 0x1ffffc001fff87ff 0xe3ffff8003fff0ff

def z705 : W := mkw 0x8008c09200000000 0x9001181240000000 0x4218418200000000 0x0843083040000000

def z706 : W := mkw 0x02221a4983264626 0x204443493064c8c4 0x1da6b84187760603 0x63b4d70830eec0c0

def z707 : W := mkw 0x800ad2db00000000 0xb0015a5b60000000 0xff9fffffe0000000 0x1ff3fffffc000000

def z708 : W := mkw 0xb01dec921eed0000 0xd603bd9243dda000 0x1fbfff9c1fff8003 0xe3f7fff383fff000

def z709 : W := mkw 0x323ff64d9ddb6666 0xe647fec9b3bb6ccc 0xa219465d9889e664 0x944328cbb3113ccc

def z710 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xff9fffffe0080002 0xbff3fffffc010000

def z711 : W := mkw 0xc01737fb40000000 0x7802e6ff68000000 0xe0063bffe0000000 0x1c00c77ffc000000

def z712 : W := mkw 0xc01ff7fb41004400 0xf803feff68200880 0xff9fffffe7006000 0x5ff3fffffce00c00

def z713 : W := mkw 0xe01ff7fb48480000 0xfc03feff69090000 0xffbffffff8ff8003 0xfff7ffffff1ff000

def z714 : W := mkw 0xc000349b40000000 0x5800069368000000 0x90003c1fe0000000 0x12000783fc000000

def z715 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0x0178839c1870787c 0x402f1073830e0f0f

def z716 : W := mkw 0x0a35192d96b63366 0x0146a325b2d6c66c 0xda79b9bd98f619e2 0x9b4f3737b31ec33c

def z717 : W := mkw 0x4817376955805500 0x6902e6ed2ab00aa0 0xffdfbffdff807f85 0xfffbf7ffbff00ff0

def z718 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xff9fffffe7000001 0x7ff3fffffce00000

def z719 : W := mkw 0xc01ff7fb54800000 0xf803feff6a900000 0xffdfffffff800785 0xfffbfffffff000f0

def z720 : W := mkw 0xc01737fb40000000 0x7802e6ff68000000 0x94073c7fe0000000 0x1280e78ffc000000

def z721 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0x1da6ba5d87766603 0x63b4d74bb0eeccc0

def z722 : W := mkw 0x0220180d82362266 0x00440301b046c44c 0x9926b81d87760062 0x5324d703b0eec00c

def z723 : W := mkw 0x0000100900000000 0x0000020120000000 0xfe81fc7fe0000000 0x1fd03f8ffc000000

def z724 : W := mkw 0xf41ff7fb5cc90810 0xfe83feff6b992102 0xffdffffff8899818 0x9ffbffffff113303

def z725 : W := mkw 0x02221a4d03346442 0x20444349a0668c88 0x3da6ba5c07766607 0x67b4d74b80eeccc0

def z726 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x113ebc001f778000 0x4227d78003eef000

def z727 : W := mkw 0xc008f49b40000000 0xd8011e9368000000 0x9c01fc7fe0000000 0x13803f8ffc000000

def z728 : W := mkw 0xc01ff7fb55804400 0xf803feff6ab00880 0xff9fffffff806605 0xfff3fffffff00cc0

def z729 : W := mkw 0xa62adadb8b6e4e36 0xb4c55b5b716dc9c6 0x565e79c39f0e1e19 0x8acbcf3873e1c3c3

def z730 : W := mkw 0xf01dedb25eed0000 0xde03bdb64bdda000 0xffbffde3ffff8003 0xfff7ffbc7ffff000

def z731 : W := mkw 0xe41ff7fb48480810 0xfc83feff69090102 0xff9fffffe0080018 0x1ff3fffffc010003

def z732 : W := mkw 0xc81737fb55805500 0x7902e6ff6ab00aa0 0xf7df3fffff807f85 0xfefbe7fffff00ff0

def z733 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x1fbffc001f7f8002 0x43f7ff8003eff000

def z734 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0x0bf8c39c1878787e 0xe17f1873830f0f0f

def z735 : W := mkw 0xe01ff7fb48480000 0xfc03feff69090000 0xff9ffffff8080000 0x9ff3ffffff010000

def z736 : W := mkw 0x0a221b6d03347542 0x2144436da0668ea8 0x0126bb9c07707800 0x4024d77380ee0f00

def z737 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0xbfbffc001fff8067 0xf7f7ff8003fff00c

def z738 : W := mkw 0x4817376955805500 0x6902e6ed2ab00aa0 0x67df3be01f807f85 0xecfbe77c03f00ff0

def z739 : W := mkw 0x02221a4d82362266 0x20444349b046c44c 0xbda6ba5d87760063 0x77b4d74bb0eec00c

def z740 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0x4378c39e1878787e 0xe86f1873c30f0f0f

def z741 : W := mkw 0xf0021bfb5eed0000 0x3e00437f6bdda000 0xe02003ffffff8003 0xfc04007ffffff000

def z742 : W := mkw 0x6417376d48582850 0x6c82e6eda90b050a 0x14673c61f878787e 0xe28ce78c3f0f0f0f

def z743 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xb926ba5d87766666 0x5724d74bb0eecccc

def z744 : W := mkw 0xc81ff7fb41005500 0xf903feff68200aa0 0xff9fffffe0000780 0x1ff3fffffc0000f0

def z745 : W := mkw 0x00021a4902240000 0x2000434920448000 0x0126ba1c07700000 0x4024d74380ee0000

def z746 : W := mkw 0xc81ff7fb54801100 0xf903feff6a900220 0xff9ffffff8001800 0x1ff3ffffff000300

def z747 : W := mkw 0xc11ff7fbe00282ac 0xf823feff7c005055 0x015ebb9c008f87ff 0xa02bd7738011f0ff

def z748 : W := mkw 0x01000000a00282ac 0x0020000014005055 0xfa414463e08f87fe 0x9f48288c7c11f0ff

def z749 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x475f03e01f807f81 0xc8ebe07c03f00ff0

def z750 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xbda6fe5fe7766667 0x77b4dfcbfceecccc

def z751 : W := mkw 0xe408f49b48480810 0xdc811e9369090102 0x9800fc1fe0080018 0x13001f83fc010003

def z752 : W := mkw 0xf11de5b2fccb82ac 0xde23bcb65f997055 0xfed945e3f88f87ff 0xbfdb28bc7f11f0ff

def z753 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0xfff8c3df9878787e 0xffff187bf30f0f0f

def z754 : W := mkw 0x300008000a6d0000 0x06000100014da000 0x1da6b800077f8003 0x63b4d70000eff000

def z755 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xff9fffffe0898000 0x9ff3fffffc113000

def z756 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xbda7be7de7766667 0x77b4f7cfbceecccc

def z757 : W := mkw 0x0800000015805500 0x0100000002b00aa0 0x425801801f807f85 0xe84b003003f00ff0

def z758 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0xebf8c39e1870787c 0x5d7f1873c30e0f0f

def z759 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xfde6bbdd87767e67 0x7fbcd77bb0eecfcc

def z760 : W := mkw 0x300008001eed0000 0x0600010003dda000 0x1fa7fc001fff8003 0xe3f4ff8003fff000

def z761 : W := mkw 0x381dec001eed1100 0xc703bd8003dda220 0x1ffffc001fff9983 0xe3ffff8003fff330

def z762 : W := mkw 0xc00af7fb40000000 0xf8015eff68000000 0xfb98ffffe0000000 0x1f731ffffc000000

def z763 : W := mkw 0x02221a4d03346442 0x20444349a0668c88 0x1926ba1c07766002 0x4324d74380eecc00

def z764 : W := mkw 0x4002136940000000 0x2800426d28000000 0xbd86ba7de0000000 0x17b0d74fbc000000

def z765 : W := mkw 0xe01ff7fb5cc80000 0xfc03feff6b990000 0xffbffffffff80003 0xfff7ffffffff0000

def z766 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xffdfffffe0800180 0x9ffbfffffc100030

def z767 : W := mkw 0x872212dfa112eefe 0x30e4425bf4225ddf 0xe04003ffe0007ffc 0x1c08007ffc000fff

def z768 : W := mkw 0xc32213ffe112e6ee 0x3864427ffc225cdd 0xe04003ffe00067fc 0x1c08007ffc000cff

def z769 : W := mkw 0x380aef600b6d5500 0xe7015dec016daaa0 0x7860ffe0007fff86 0x0f0c1ffc000ffff0

def z770 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xffdfffffe08f8787 0xbffbfffffc11f0f0

def z771 : W := mkw 0xc01df5bb40000000 0xd803beb768000000 0x9818fd9fe0000000 0x13031fb3fc000000

def z772 : W := mkw 0xc81ff7fb55805500 0xf903feff6ab00aa0 0xffdfffffff887fff 0xfffbfffffff10fff

def z773 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x1b3ffc001fff8002 0xc367ff8003fff000

def z774 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x615e03e01f807f85 0xec2bc07c03f00ff0

def z775 : W := mkw 0xec1ff7fb5dc85d10 0xfd83feff6bb90ba2 0xffdfffffff887f9d 0xfffbfffffff10ff3

def z776 : W := mkw 0x02221a4d03346442 0x20444349a0668c88 0x1fa7fe1c07ffe003 0xe3f4ffc380fffc00

def z777 : W := mkw 0x2008c8000a6c0000 0x84011900014d8000 0x1fbffc001fff8003 0xe3f7ff8003fff000

def z778 : W := mkw 0xc00ad3fb40000000 0xb8015a7f68000000 0xff9efbffe0000000 0x1ff3df7ffc000000

def z779 : W := mkw 0xb01dec921eed0000 0xd603bd9243dda000 0x9fbffc1e1fff8003 0xf3f7ff83c3fff000

def z780 : W := mkw 0xf01ff7fb5cc90000 0xfe03feff6b992000 0xff9ffffff8000000 0x1ff3ffffff000000

def z781 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xff9fffffe0800001 0xbff3fffffc100000

def z782 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0xffffff821ffff87f 0xfffffff043ffff0f

def z783 : W := mkw 0x02221a4d03346442 0x20444349a0668c88 0xbda6ba5d87766003 0x77b4d74bb0eecc00

def z784 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x5ffffd801fff9803 0xebffffb003fff300

def z785 : W := mkw 0xc00af7fb40000000 0xf8015eff68000000 0x9800fc7fe0000000 0x13001f8ffc000000

def z786 : W := mkw 0x30152c001eed0000 0x4602a58003dda000 0x1ea77c001fff8003 0xe3d4ef8003fff000

def z787 : W := mkw 0x0817136915805500 0x2102e26d22b00aa0 0xffdfffffff807f85 0xfffbfffffff00ff0

def z788 : W := mkw 0xc01ff7fb54800000 0xf803feff6a900000 0xff9fffffe7800001 0x1ff3fffffcf00000

def z789 : W := mkw 0x09170360b582d7ac 0x2122e06c16b05af5 0x991e4783ff0ff87a 0x5323c8f07fe1ff0f

def z790 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xeb9efbffe0000000 0x1d73df7ffc000000

def z791 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0x0126ba5d87706600 0x4024d74bb0ee0cc0

def z792 : W := mkw 0xc00237fb40000000 0x780046ff68000000 0xf0003fffe0000000 0x1e0007fffc000000

def z793 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0x011ebbfde0000000 0x0023d77fbc000000

def z794 : W := mkw 0xbc1de5b21cc91910 0xd783bcb643992322 0x425945a218899998 0x884b28b443113333

def z795 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0xebf8c39e18fff87f 0xfd7f1873c31fff0f

def z796 : W := mkw 0xc01737fb40000000 0x7802e6ff68000000 0xfe877fffe0000000 0x1fd0effffc000000

def z797 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x6fff83e01ff07f87 0xedfff07c03fe0ff0

def z798 : W := mkw 0x03220a44a336e6ee 0x206441489466dcdd 0x67e7026007ffe7ff 0xecfce04c00fffcff

def z799 : W := mkw 0x0817136915805500 0x2102e26d22b00aa0 0x77df3be19f807f85 0xeefbe77c33f00ff0

def z800 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x65de03e01f007f85 0x6cbbc07c03e00ff0

def z801 : W := mkw 0xb01dec921eed0000 0xd603bd9243dda000 0xffffff9e1fff807f 0xfffffff3c3fff00f

def z802 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0xfff8c39e187e787f 0xffff1873c30fcf0f

def z803 : W := mkw 0xf01dedb25eed0000 0xde03bdb64bdda000 0x1fbffd801fff8003 0xe3f7ffb003fff000

def z804 : W := mkw 0x381ded201eed1100 0xc703bda403dda220 0x7ffffde01fff9f87 0xefffffbc03fff3f0

def z805 : W := mkw 0x02221a4d03346442 0x20444349a0668c88 0x21a6ba1c07706004 0x6434d74380ee0c00

def z806 : W := mkw 0xc01ff7fb54800000 0xf803feff6a900000 0xffdfffffff807805 0xfffbfffffff00f00

def z807 : W := mkw 0xb41dec921eed0810 0xd683bd9243dda102 0x1fbffd801fff9803 0xe3f7ffb003fff300

def z808 : W := mkw 0xc00213fb40000000 0x3800427f68000000 0xf4063bffe0000000 0x1e80c77ffc000000

def z809 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xffbebbdd87766667 0x7ff7d77bb0eecccc

def z810 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x7fffffe01fffff87 0xeffffffc03fffff0

def z811 : W := mkw 0x03200804a236a2ee 0x006401009446d45d 0x0060000000ff87ff 0xa00c0000001ff0ff

def z812 : W := mkw 0x701ded205eed0000 0xce03bda40bdda000 0x1fbffc207fff8003 0xe3f7ff840ffff000

def z813 : W := mkw 0x0000080002240000 0x0000010000448000 0x1da6fc00077f8003 0x63b4df8000eff000

def z814 : W := mkw 0x0815012015805500 0x0102a02402b00aa0 0x005801801f807f85 0xe00b003003f00ff0

def z815 : W := mkw 0x02221a4d03346442 0x20444349a0668c88 0x63febb9c1f707804 0xec7fd77383ee0f00

def z816 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x011e03e01f007f80 0x4023c07c03e00ff0

def z817 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x67df03e01f8fff87 0xecfbe07c03f1fff0

def z818 : W := mkw 0xc008f49b40000000 0xd8011e9368000000 0xfbd8ff9ff8007804 0xff7b1ff3ff000f00

def z819 : W := mkw 0xc81ff7fb55805500 0xf903feff6ab00aa0 0xffdffffff8807f84 0x9ffbffffff100ff0

def z820 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0xefdf83fc1f807f85 0xfdfbf07f83f00ff0

def z821 : W := mkw 0x0817136915805500 0x2102e26d22b00aa0 0x67dfbbfc1f807f85 0xecfbf77f83f00ff0

def z822 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xbde6ba5d9f767e67 0xf7bcd74bb3eecfcc

def z823 : W := mkw 0x001dec0002240000 0xc003bd8000448000 0x1fbffc0007ff8003 0xe3f7ff8000fff000

def z824 : W := mkw 0xe408e49648582850 0xdc811c92c90b050a 0xebf8c79e7878787e 0xfd7f18f3cf0f0f0f

def z825 : W := mkw 0x0800000015805500 0x0100000002b00aa0 0x67d903e01f807f85 0xecfb207c03f00ff0

def z826 : W := mkw 0x02221a4d03346442 0x20444349a0668c88 0xa126ba5d87706000 0x5424d74bb0ee0c00

def z827 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x9fbffc03ffff8003 0xf3f7ff807ffff000

def z828 : W := mkw 0x4000340940000000 0x4800068128000000 0x9800bc1de0000000 0x13001783bc000000

def z829 : W := mkw 0xf01dec925eed0000 0xde03bd924bdda000 0x1fbffc027fff8003 0xe3f7ff804ffff000

def z830 : W := mkw 0x06221a4d83366e76 0x20c44349b066cdce 0xbde6ba5d87767e7f 0x77bcd74bb0eecfcf

def z831 : W := mkw 0x01000000a00282ac 0x0020000014005055 0xfed945e3f88f9fff 0xbfdb28bc7f11f3ff

def z832 : W := mkw 0x10152c0016a50000 0x4202a58002d4a000 0x14273c0007f78003 0x6284e78000fef000

def z833 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0xa9f8839c1878787e 0xf53f1073830f0f0f

def z834 : W := mkw 0xc81ff7fb55805500 0xf903feff6ab00aa0 0x9c07fc7fe7800781 0x1380ff8ffcf000f0

def z835 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0xe178839e1878787e 0xfc2f1073c30f0f0f

def z836 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xffe7fa7f87fe67ff 0xfffcff4ff0ffccff

def z837 : W := mkw 0xc00af6db40000000 0xf8015edb68000000 0xff87fe7fe0000000 0x1ff0ffcffc000000

def z838 : W := mkw 0x4817376955805500 0x6902e6ed2ab00aa0 0xbd87be7de7806785 0x77b0f7cfbcf00cf0

def z839 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xfffefbdf9f7e7e7f 0xffffdf7bf3efcfcf

def z840 : W := mkw 0xc01df49b40000000 0xd803be9368000000 0xff9fff9fe0000000 0x1ff3fff3fc000000

def z841 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0x25a6ba5c07766667 0x64b4d74b80eecccc

def z842 : W := mkw 0x10152c0016a50000 0x4202a58002d4a000 0x1fbfbc001ff78003 0xe3f7f78003fef000

def z843 : W := mkw 0xc808f49b55805500 0xd9011e936ab00aa0 0x9840fc1fff807f85 0xf3081f83fff00ff0

def z844 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xf51fbfffe0000000 0x1ea3f7fffc000000

def z845 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0x1da6ba1c07766667 0x63b4d74380eecccc

def z846 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xffbfffffe0700002 0x7ff7fffffc0e0000

def z847 : W := mkw 0xc80213fb41005500 0x3900427f68200aa0 0xfdc6bbffe7007f85 0x7fb8d77ffce00ff0

def z848 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0xea78c39e1878787e 0x9d4f1873c30f0f0f

def z849 : W := mkw 0xe41ff7fb48480810 0xfc83feff69090102 0xffdffffff808781c 0xfffbffffff010f03

def z850 : W := mkw 0x8400009600102850 0x10800012c002050a 0xebf8839e1870787e 0xfd7f1073c30e0f0f

def z851 : W := mkw 0x02221a4d03346442 0x20444349a0668c88 0x67e7ba7c07f06785 0xecfcf74f80fe0cf0

def z852 : W := mkw 0x0220180d83366666 0x00440301b066cccc 0x9da6b81d87766667 0x73b4d703b0eecccc

def z853 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0x1526ba5d87766667 0x62a4d74bb0eecccc

def z854 : W := mkw 0xb51de492bccb8abc 0xd6a3bc9257997157 0xfed945e3f88f9fff 0xbfdb28bc7f11f3ff

def z855 : W := mkw 0x311dec00beef82ac 0xc623bd8017ddf055 0xe17eb863ff7007fc 0x5c2fd70c7fee00ff

def z856 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0x1f9ffffde0000000 0x03f3ffffbc000000

def z857 : W := mkw 0xb41dec921eed0810 0xd683bd9243dda102 0xffffff9e1fff981b 0xfffffff3c3fff303

def z858 : W := mkw 0xc81ff7fb41005500 0xf903feff68200aa0 0xffdffffff8007f84 0xfffbffffff000ff0

def z859 : W := mkw 0x3008ec000a6d0000 0xc6011d80014da000 0x1926fc00077f8002 0x4324df8000eff000

def z860 : W := mkw 0x0220180d02342042 0x00440301a0468408 0x0126b81c07700000 0x4024d70380ee0000

def z861 : W := mkw 0xc81ff7fb55805500 0xf903feff6ab00aa0 0xffdfffffff007f84 0x5ffbffffffe00ff0

def z862 : W := mkw 0x30152c001eed0000 0x4602a58003dda000 0x1da7bc001fff8003 0xe3b4f78003fff000

def z863 : W := mkw 0xc01df49b40000000 0xd803be9368000000 0x9c07fc1fe0000000 0x1380ff83fc000000

def z864 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x033ffc001fff8003 0xe067ff8003fff000

def z865 : W := mkw 0x03200804a336e6ee 0x006401009466dcdd 0x00600000077667ff 0x600c000000eeccff

def z866 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xbfbeba5d9f766667 0xf7f7d74bb3eecccc

def z867 : W := mkw 0x10152c0016a50000 0x4202a58002d4a000 0x1527bc0007f78001 0x42a4f78000fef000

def z868 : W := mkw 0xe01ff7fb48480000 0xfc03feff69090000 0xffbffffff8700000 0x5ff7ffffff0e0000

def z869 : W := mkw 0x94152c9616b52850 0x5282a592c2d6a50a 0xf4473f9e0787f87d 0x1e88e7f3c0f0ff0f

def z870 : W := mkw 0x341dec001eed0810 0xc683bd8003dda102 0x1ffffc001fff981b 0xe3ffff8003fff303

def z871 : W := mkw 0x03221a4da336e6ee 0x20644349b466dcdd 0x1527be7de7f7e781 0x42a4f7cfbcfefcf0

def z872 : W := mkw 0x0002124900000000 0x2000424920000000 0xbd86fe5fe0000000 0x17b0dfcbfc000000

def z873 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xbda6ba5d87760663 0x17b4d74bb0eec0cc

def z874 : W := mkw 0x10152c0016a50000 0x4202a58002d4a000 0x1fa7fc0007ff8003 0xe3f4ff8000fff000

def z875 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0x0126ba1c07766062 0x4024d74380eecc0c

def z876 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x435f03a01f807f85 0xe86be07403f00ff0

def z877 : W := mkw 0xc81ff7fb55805500 0xf903feff6ab00aa0 0xff9fffffff007e05 0x7ff3ffffffe00fc0

def z878 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xbfa7ba5d87f66667 0xf7f4f74bb0fecccc

def z879 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0x9d26ba5d87766663 0x53a4d74bb0eecccc

def z880 : W := mkw 0x401ff76940000000 0xe803feed28000000 0xbf9ffe7de0000000 0x17f3ffcfbc000000

def z881 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xfde6ba5f8776667f 0x7fbcd74bf0eecccf

def z882 : W := mkw 0xe408f49b48480810 0xdc811e9369090102 0xda58fd9ff8081818 0x9b4b1fb3ff010303

def z883 : W := mkw 0x02221a4d03346442 0x20444349a0668c88 0x2126ba5c07706604 0x4424d74b80ee0cc0

def z884 : W := mkw 0xb41de4921cc90810 0xd683bc9243992102 0x0018018018001800 0x0003003003000300

def z885 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0xe978c39e1878787e 0x5d2f1873c30f0f0f

def z886 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0xfffffc63ffff8787 0xffffff8c7ffff0f0

def z887 : W := mkw 0xb41dec921eed0810 0xd683bd9243dda102 0xfffffd821fff987f 0xffffffb043fff30f

def z888 : W := mkw 0x10152c0016a50000 0x4202a58002d4a000 0x1c27bc0007f78003 0x0384f78000fef000

def z889 : W := mkw 0x01000000a00282ac 0x0020000014005055 0xf6414463e08f87fd 0x9ec8288c7c11f0ff

def z890 : W := mkw 0xac1fc3f61dd87d50 0xb583f87ec3bb0faa 0x8c27c07e07f807fb 0x1184f80fc0ff00ff

def z891 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xbda6ba5d87ffe667 0xf7b4d74bb0fffccc

def z892 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0xffdf03e19f807f85 0xfffbe07c33f00ff0

def z893 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0x1426b85d87760601 0x0284d70bb0eec0c0

def z894 : W := mkw 0xc81ff7fb55805500 0xf903feff6ab00aa0 0xe15ebbffff007f84 0x5c2bd77fffe00ff0

def z895 : W := mkw 0xc01737fb40000000 0x7802e6ff68000000 0x14073ffde0000000 0x0280e7ffbc000000

def z896 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x465f01e01f807f85 0xe8cbe03c03f00ff0

def z897 : W := mkw 0xe41ff7fb48480810 0xfc83feff69090102 0xffdffffff808187e 0xbffbffffff01030f

def z898 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xfb9eff9fe0000000 0x1f73dff3fc000000

def z899 : W := mkw 0x3008ec000a6d0000 0xc6011d80014da000 0x1fa7fc0007ff8003 0xe3f4ff8000fff000

def z900 : W := mkw 0x01000000a00282ac 0x0020000014005055 0xffd947e3e08f87ff 0xbffb28fc7c11f0ff

def z901 : W := mkw 0xc01ff7fb41004400 0xf803feff68200880 0xffdfffffe7806785 0xfffbfffffcf00cf0

def z902 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0x9da6ba1d87766063 0x73b4d743b0eecc0c

def z903 : W := mkw 0xc23dedb6c3366666 0xd847bdb6d866cccc 0x423945a267766667 0x684728b44ceecccc

def z904 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0x111ebf9de0000000 0x0223d7f3bc000000

def z905 : W := mkw 0x02221a4d03346442 0x20444349a0668c88 0xbda6ba1c07766067 0x77b4d74380eecc0c

def z906 : W := mkw 0xa408e49608582850 0xd4811c92c10b050a 0xfbf8ff9e1878787e 0xff7f1ff3c30f0f0f

def z907 : W := mkw 0xf01de4925cc90000 0xde03bc924b992000 0x0219440278898000 0x804328804f113000

def z908 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0xffdf47e3ff887fff 0xfffbe8fc7ff10fff

def z909 : W := mkw 0x02221a4d03346442 0x20444349a0668c88 0xbda6ba5d87706605 0x77b4d74bb0ee0cc0

def z910 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x77df07e01f87ff85 0xeefbe0fc03f0fff0

def z911 : W := mkw 0x00021a4903244400 0x2000434920648880 0xbda6ba5d87766607 0x77b4d74bb0eeccc0

def z912 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0xeffec39e1f78787f 0xfdffd873c3ef0f0f

def z913 : W := mkw 0xc00af6db41004400 0xf8015edb68200880 0xbd86fe5fe7006605 0x77b0dfcbfce00cc0

def z914 : W := mkw 0xc81ff7fb40001100 0xf903feff68000220 0xffdfffffe0001980 0x1ffbfffffc000330

def z915 : W := mkw 0xbc1dedb21eed1910 0xd783bdb643dda322 0x5ffffda21fff999b 0xebffffb443fff333

def z916 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0x9806fc1fe0000000 0x1300df83fc000000

def z917 : W := mkw 0xb01de4921cc90000 0xd603bc9243992000 0x4219458218898000 0x884328b043113000

def z918 : W := mkw 0xf01df49b5cc90000 0xde03be936b992000 0x9a19fc1ff8898000 0x93433f83ff113000

def z919 : W := mkw 0xc81ff7fb41005500 0xf903feff68200aa0 0xff9fffffe0007800 0x1ff3fffffc000f00

def z920 : W := mkw 0xc01df49b40000000 0xd803be9368000000 0x991efc1fe0000000 0x1323df83fc000000

def z921 : W := mkw 0x4817376955805500 0x6902e6ed2ab00aa0 0xffdf7fe3ff807f85 0xfffbeffc7ff00ff0

def z922 : W := mkw 0x30152c001eed0000 0x4602a58003dda000 0x14273c001ff78001 0x4284e78003fef000

def z923 : W := mkw 0x03221a4da336e6ee 0x20644349b466dcdd 0xfee7fc7fe7ff87ff 0xbfdcff8ffcfff0ff

def z924 : W := mkw 0x02221a4d03346442 0x20444349a0668c88 0xa9a6ba1c07706000 0x5534d74380ee0c00

def z925 : W := mkw 0xc81ff7fb54801100 0xf903feff6a900220 0xffdffffff8801f85 0xbffbffffff1003f0

def z926 : W := mkw 0x01000000a00282ac 0x0020000014005055 0xfec147e3e08fffff 0xbfd828fc7c11ffff

def z927 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xa5a6ba5d87706665 0x74b4d74bb0ee0ccc

def z928 : W := mkw 0x3008c8001eed0000 0x8601190003dda000 0x1fbef8001fff8003 0xe3f7df0003fff000

def z929 : W := mkw 0x00020a4403346440 0x2000414880668c88 0xbda6ba5c07766667 0x77b4d74b80eecccc

def z930 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xbda6fa5f877e667f 0x77b4df4bf0efcccf

def z931 : W := mkw 0x0802024015805500 0x2100404802b00aa0 0x67de03c01f807f85 0xecfbc07803f00ff0

def z932 : W := mkw 0xc008f49b40000000 0xd8011e9368000000 0xf800ff9fe0000000 0x1f001ff3fc000000

def z933 : W := mkw 0x02221a4d03346442 0x20444349a0668c88 0x9926ba1d87706000 0x5324d743b0ee0c00

def z934 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xffe7fe5f87ffe67f 0xfffcffcbf0fffccf

def z935 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x1fbffc61ffff8003 0xe3f7ff8c3ffff000

def z936 : W := mkw 0xf01de5b25cc90000 0xde03bcb64b992000 0x0018018018000000 0x0003003003000000

def z937 : W := mkw 0x0b200804b7b6f7ee 0x0164010096f6defd 0x006000001fffffff 0xe00c000003ffffff

def z938 : W := mkw 0xc01df5bb40000000 0xd803beb768000000 0xfb99ffbfe0000000 0x1f733ff7fc000000

def z939 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xfc07ffffe0000000 0x1f80fffffc000000

def z940 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x013eb8001f7f8002 0x4027d70003eff000

def z941 : W := mkw 0x0002124900000000 0x2000424920000000 0xbd87be7de0000000 0x17b0f7cfbc000000

def z942 : W := mkw 0xc01df5bb40000000 0xd803beb768000000 0xdf9ffdbfe0000000 0x1bf3ffb7fc000000

def z943 : W := mkw 0x02221a4d03346442 0x20444349a0668c88 0x05a6ba1c07706001 0x60b4d74380ee0c00

def z944 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x1ffffc001ffff807 0xe3ffff8003ffff00

def z945 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xdb1fffbfe0000000 0x1b63fff7fc000000

def z946 : W := mkw 0x27200804ab7eeefe 0x04e40100956fdddf 0x006000001fffffff 0xe00c000003ffffff

def z947 : W := mkw 0x0000080482362264 0x000001009046c44c 0xbda6ba5d87766667 0x77b4d74bb0eecccc

def z948 : W := mkw 0x0000080002240000 0x0000010000448000 0x1da7bc0007f78003 0x63b4f78000fef000

def z949 : W := mkw 0x10002c0002250000 0x420005800044a000 0x1da6bc0007778003 0x63b4d78000eef000

def z950 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xbde6ba5d877e667f 0xf7bcd74bb0efcccf

def z951 : W := mkw 0xf41dedb25eed0810 0xde83bdb64bdda102 0x5ffffda27fff981b 0xebffffb44ffff303

def z952 : W := mkw 0x0b370b64b7b6f7ee 0x2166e16c96f6defd 0x67ff03e01fffffff 0xecffe07c03ffffff

def z953 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0x9da6b85d87760663 0x73b4d70bb0eec0cc

def z954 : W := mkw 0x01000804a236a2ec 0x002001009446d45d 0xffe7fe7fe7ffe7ff 0xfffcffcffcfffcff

def z955 : W := mkw 0xf01ff7fb5cc90000 0xfe03feff6b992000 0xff9ffffff88f8003 0xbff3ffffff11f000

def z956 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x25de03c01f807f85 0xe4bbc07803f00ff0

def z957 : W := mkw 0x0800000015805500 0x0100000002b00aa0 0x015803801f807f85 0xe02b007003f00ff0

def z958 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0x8126ba1d87706060 0x5024d743b0ee0c0c

def z959 : W := mkw 0x03221a4da336e6ee 0x20644349b466dcdd 0xffa7fe7fe77fe67f 0x7ff4ffcffceffccf

def z960 : W := mkw 0x01000000a00282ac 0x0020000014005055 0x9e814463e08f87fb 0xb3d0288c7c11f0ff

def z961 : W := mkw 0x02221a4983264626 0x204443493064c8c4 0xbda6ba5d87760603 0x77b4d74bb0eec0c0

def z962 : W := mkw 0x300008001eed0000 0x0600010003dda000 0x0126b8001fff8003 0xe024d70003fff000

def z963 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xbda7ba7d87f667e7 0x77b4f74fb0feccfc

def z964 : W := mkw 0xb41dec921eed0810 0xd683bd9243dda102 0x7fffff821ffff81f 0xeffffff043ffff03

def z965 : W := mkw 0xc01df5bb40000000 0xd803beb768000000 0x9801fc3fe0000000 0x13003f87fc000000

def z966 : W := mkw 0xa508c096a85aaafc 0x94a11812d50b555f 0x153987fdf8f7ff81 0x42a730ffbf1efff0

def z967 : W := mkw 0x03221a4da336e6ee 0x20644349b466dcdd 0xbda7fe7fe7ffe7ff 0x77b4ffcffcfffcff

def z968 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x5ffffc021fff801b 0xebffff8043fff003

def z969 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xbdbebbdd9f767e67 0x77b7d77bb3eecfcc

def z970 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x07df03801f807f85 0xe0fbe07003f00ff0

def z971 : W := mkw 0x01000000a00282ac 0x0020000014005055 0xbc814463e08f87ff 0x3790288c7c11f0ff

def z972 : W := mkw 0x03221a4da336e6ee 0x20644349b466dcdd 0xffe6fe5fe77fe67f 0xfffcdfcbfceffccf

def z973 : W := mkw 0x0322124da112e6ee 0x20644249b4225cdd 0xa000025fe000667c 0x1400004bfc000ccf

def z974 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xffffbbfd9ff67fe7 0xfffff77fb3fecffc

def z975 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xffdfffffe08f807f 0xbffbfffffc11f00f

def z976 : W := mkw 0x03221a4da336e6ee 0x20644349b466dcdd 0xffe6fa7fe77e67ff 0xfffcdf4ffcefccff

def z977 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x9fbffc021fff807b 0xf3f7ff8043fff00f

def z978 : W := mkw 0x03221a4da336e6ee 0x20644349b466dcdd 0xffa7fe7fe7f7e7e7 0x7ff4ffcffcfefcfc

def z979 : W := mkw 0x0b371b69b7a6d7ae 0x2166e36d36f4daf5 0x14073c61e7878781 0x0280e78c3cf0f0f0

def z980 : W := mkw 0xe41ff7fb48480810 0xfc83feff69090102 0xff9ffffff8001800 0x1ff3ffffff000300

def z981 : W := mkw 0x30152c001eed0000 0x4602a58003dda000 0x002638001fff8003 0xe004c70003fff000

def z982 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0xeff9c3fe1878787e 0xfdff387fc30f0f0f

def z983 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xa126ba5d87766667 0x7424d74bb0eecccc

def z984 : W := mkw 0xc008f49b40000000 0xd8011e9368000000 0xb980fe1fe0000000 0x17301fc3fc000000

def z985 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xf91effffe0000000 0x1f23dffffc000000

def z986 : W := mkw 0x01000000a00282ac 0x0020000014005055 0xde414463e08f87fb 0x9bc8288c7c11f0ff

def z987 : W := mkw 0x0815012015805500 0x0102a02402b00aa0 0x47df01a01f807f85 0xe8fbe03403f00ff0

def z988 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x1ea7fc0007ff8003 0xa3d4ff8000fff000

def z989 : W := mkw 0xc008f49b40000000 0xd8011e9368000000 0x9d86fc1fe0000000 0x13b0df83fc000000

def z990 : W := mkw 0xc00af6db40000000 0xf8015edb68000000 0x9906fe1fe0000000 0x1320dfc3fc000000

def z991 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xbd87fe7fe0000000 0x17b0ffcffc000000

def z992 : W := mkw 0x001ff64900000000 0xe003fec920000000 0xff9ffe7fe0000000 0x1ff3ffcffc000000

def z993 : W := mkw 0xf01dedb25eed0000 0xde03bdb64bdda000 0xffbfffbe7fff8003 0xfff7fff7cffff000

def z994 : W := mkw 0x381ded201eed1100 0xc703bda403dda220 0x1fbffd801fff9803 0xe3f7ffb003fff300

def z995 : W := mkw 0x0002124900000000 0x2000424920000000 0xfd86ba7fe0000000 0x1fb0d74ffc000000

def z996 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xf61f7fffe0000000 0x1ec3effffc000000

def z997 : W := mkw 0xc81ff7fb41005500 0xf903feff68200aa0 0xffdfffffe0807f85 0xbffbfffffc100ff0

def z998 : W := mkw 0x02221a4d03346442 0x20444349a0668c88 0x0126ba1c07766003 0x6024d74380eecc00

def z999 : W := mkw 0x0322124da112e6ee 0x20644249b4225cdd 0xa000027de00067e4 0x1400004fbc000cfc

def z1000 : W := mkw 0x01000000a00282ac 0x0020000014005055 0xfc414463e08f87ff 0x1f88288c7c11f0ff

def z1001 : W := mkw 0x02221b6d83366666 0x2044436db066cccc 0xfda6bbfd87766667 0x7fb4d77fb0eecccc

def z1002 : W := mkw 0xc00213fb40000000 0x3800427f68000000 0xff87ffffe0000000 0x1ff0fffffc000000

def z1003 : W := mkw 0x42221b6dc3366666 0x2844436db866cccc 0xbda6ba7de7766667 0x77b4d74fbceecccc

def z1004 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x1fbffc601fff8783 0xe3f7ff8c03fff0f0

def z1005 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0x0126ba1c07706664 0x4024d74380ee0ccc

def z1006 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x1c27fc001fff8003 0xe384ff8003fff000

def z1007 : W := mkw 0x03221a4da336e6ee 0x20644349b466dcdd 0x0166ba1c07ffe7ff 0xe02cd74380fffcff

def z1008 : W := mkw 0x0b22136da112f7ee 0x2164426db4225efd 0xe04003ffe0007ffc 0x1c08007ffc000fff

def z1009 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x625903e01f807f85 0xec4b207c03f00ff0

def z1010 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0x811ebb9fe0000000 0x1023d773fc000000

def z1011 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xffdfffffe0000784 0x1ffbfffffc0000f0

def z1012 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0x35a6ba5d87766605 0x66b4d74bb0eeccc0

def z1013 : W := mkw 0x4017376940000000 0x6802e6ed28000000 0x1507be7de0000000 0x02a0f7cfbc000000

def z1014 : W := mkw 0xc008f5bb40000000 0xd8011eb768000000 0xd800fdbfe0000000 0x1b001fb7fc000000

def z1015 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0xfffffc63ffff807f 0xffffff8c7ffff00f

def z1016 : W := mkw 0xc01ff7fb41004400 0xf803feff68200880 0xff9fffffe0006604 0x1ff3fffffc000cc0

def z1017 : W := mkw 0x02221a4d03346442 0x20444349a0668c88 0x0526ba5c07706601 0x40a4d74b80ee0cc0

def z1018 : W := mkw 0x0015000014800000 0x0002a00002900000 0x67df03e01f807f85 0xecfbe07c03f00ff0

def z1019 : W := mkw 0xa728d89faa7eaafe 0x94e51b13f54fd55f 0x9820fc1fe07f807a 0x13041f83fc0ff00f

def z1020 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xff9fffffe0000605 0x3ff3fffffc0000c0

def z1021 : W := mkw 0xc00213fb40000000 0x3800427f68000000 0xe106bbffe0000000 0x1c20d77ffc000000

def z1022 : W := mkw 0x0000080002240000 0x0000010000448000 0x1da6b80007ff8003 0xe3b4d70000fff000

def z1023 : W := mkw 0xa400009608582850 0x14800012c10b050a 0xe3f8039e1878787e 0xfc7f0073c30f0f0f

def z1024 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0xffdf47e21f8fffff 0xfffbe8fc43f1ffff

def z1025 : W := mkw 0xc008f49b40000000 0xd8011e9368000000 0x9e81fc1fe0000000 0x13d03f83fc000000

def z1026 : W := mkw 0xb01dec921eed0000 0xd603bd9243dda000 0x5fbffd821fff8003 0xebf7ffb043fff000

def z1027 : W := mkw 0xb41de4921cc90810 0xd683bc9243992102 0x0219440218898018 0x8043288043113003

def z1028 : W := mkw 0x03221a4da336e6ee 0x20644349b466dcdd 0xffe7fe7fe77667ff 0x7ffcffcffceeccff

def z1029 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x1dbeb8001fff8003 0xe3b7d70003fff000

def z1030 : W := mkw 0xc81ff7fb55805500 0xf903feff6ab00aa0 0xffdfffffff801f81 0x9ffbfffffff003f0

def z1031 : W := mkw 0x03221a4da336e6ee 0x20644349b466dcdd 0xbfa7fe7de7ffe7e7 0xf7f4ffcfbcfffcfc

def z1032 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0x1126ba1d87766000 0x4224d743b0eecc00

def z1033 : W := mkw 0xc81ff7fb41005500 0xf903feff68200aa0 0xffdfffffe7007f85 0x7ffbfffffce00ff0

def z1034 : W := mkw 0x03221a4da336e6ee 0x20644349b466dcdd 0xfde6fe7fe77fe7ff 0x7fbcdfcffceffcff

def z1035 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0x8978c39e1878787e 0xf12f1873c30f0f0f

def z1036 : W := mkw 0xb508ec96aa7faafc 0xd6a11d92d54ff55f 0x9820fc1fe07f807a 0x13041f83fc0ff00f

def z1037 : W := mkw 0xe01ff7fb48480000 0xfc03feff69090000 0xffbfffffe0780002 0x1ff7fffffc0f0000

def z1038 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xbda7be5d87f7e667 0x77b4f7cbb0fefccc

def z1039 : W := mkw 0x35000804beffaafc 0x06a0010097dff55f 0x006000001fffffff 0xe00c000003ffffff

def z1040 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x3fbffc401fff8607 0xe7f7ff8803fff0c0

def z1041 : W := mkw 0x4017376940000000 0x6802e6ed28000000 0xff87fe7fe0000000 0x1ff0ffcffc000000

def z1042 : W := mkw 0x03200804a336e6ee 0x006401009466dcdd 0x0020000007f7e7e7 0x6004000000fefcfc

def z1043 : W := mkw 0x02221a4d03346442 0x20444349a0668c88 0xa126ba1c07706064 0x5424d74380ee0c0c

def z1044 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0xebf9c79e18f9f87e 0xfd7f38f3c31f3f0f

def z1045 : W := mkw 0xc00af7fb40000000 0xf8015eff68000000 0xfd86ffffe0000000 0x1fb0dffffc000000

def z1046 : W := mkw 0x0002124901004400 0x2000424920200880 0xffc7fe7fe7806785 0xfff8ffcffcf00cf0

def z1047 : W := mkw 0x0000080402342040 0x0000010080468408 0xffe7fe1e07ffe07f 0xfffcffc3c0fffc0f

def z1048 : W := mkw 0x33200804bfffe6ee 0x0664010097fffcdd 0x006000001fffe7ff 0xe00c000003fffcff

def z1049 : W := mkw 0xe008f49b48480000 0xdc011e9369090000 0x9820fc1fe0780002 0x13041f83fc0f0000

def z1050 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xfd9ebbffe0000000 0x1fb3d77ffc000000

def z1051 : W := mkw 0xc008f49b40000000 0xd8011e9368000000 0xfec1fc7fe0800785 0xbfd83f8ffc1000f0

def z1052 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0xbfbffc419fff8003 0xf7f7ff8833fff000

def z1053 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0xfff9c79e1878787e 0xffff38f3c30f0f0f

def z1054 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0xebf8c3fff878787e 0xfd7f187fff0f0f0f

def z1055 : W := mkw 0x30152c001eed0000 0x4602a58003dda000 0x17bf3c001fff8003 0xe2f7e78003fff000

def z1056 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x1ffffc001fff8787 0xe3ffff8003fff0f0

def z1057 : W := mkw 0xc81ff7fb55805500 0xf903feff6ab00aa0 0xff9fffffe7000000 0x1ff3fffffce00000

def z1058 : W := mkw 0x01000000a00282ac 0x0020000014005055 0xffc7fc63e08f87ff 0xbff8ff8c7c11f0ff

def z1059 : W := mkw 0x02221a4d03346442 0x20444349a0668c88 0xbda6ba5d87706066 0x77b4d74bb0ee0c0c

def z1060 : W := mkw 0xe01ff7fb48480000 0xfc03feff69090000 0xfffffffff8787806 0xffffffffff0f0f00

def z1061 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xbde6ba5d87f667e7 0xf7bcd74bb0feccfc

def z1062 : W := mkw 0xf01ff7fb5cc90000 0xfe03feff6b992000 0xff9fffffff898001 0xfff3fffffff13000

def z1063 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x173ffc001fff8001 0xc2e7ff8003fff000

def z1064 : W := mkw 0x4002364940000000 0x680046c928000000 0xbd86be5de0000000 0x17b0d7cbbc000000

def z1065 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xa9a6ba1c07766667 0x7534d74380eecccc

def z1066 : W := mkw 0x4017376940000000 0x6802e6ed28000000 0xff9fbffde0000000 0x1ff3f7ffbc000000

def z1067 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0xe378c39e1878787c 0xdc6f1873c30f0f0f

def z1068 : W := mkw 0xe81ff7fb5dc85500 0xfd03feff6bb90aa0 0xfffffffffff87f87 0xffffffffffff0ff0

def z1069 : W := mkw 0x0017136900000000 0x2002e26d20000000 0xff9fffffe0000000 0x1ff3fffffc000000

def z1070 : W := mkw 0x00021a4902240000 0x2000434920448000 0xbda6ba5d87700000 0x57b4d74bb0ee0000

def z1071 : W := mkw 0x02221a4d03346442 0x20444349a0668c88 0xffa7fe7fe7706000 0x5ff4ffcffcee0c00

def z1072 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0x9926ba1d87766667 0x7324d743b0eecccc

def z1073 : W := mkw 0x0000080402342040 0x0000010080468408 0xa9a6ba1c07706066 0x7534d74380ee0c0c

def z1074 : W := mkw 0x03221a4da336e6ee 0x20644349b466dcdd 0xbda6be5de777e667 0x77b4d7cbbceefccc

def z1075 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x67df47e01f89ff85 0xecfbe8fc03f13ff0

def z1076 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0x9f9fff9fe0000000 0x13f3fff3fc000000

def z1077 : W := mkw 0x0000080402342040 0x0000010080468408 0x0126ba1c07706000 0x4024d74380ee0c00

def z1078 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xffdfffffe0007804 0x1ffbfffffc000f00

def z1079 : W := mkw 0x03221a4da336e6ee 0x20644349b466dcdd 0xbda6ba7de77667e7 0x77b4d74fbceeccfc

def z1080 : W := mkw 0x03221a4da336e6ee 0x20644349b466dcdd 0xffe7be7de7f7e7e7 0xfffcf7cfbcfefcfc

def z1081 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0xfffffc621fff87ff 0xffffff8c43fff0ff

def z1082 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x259f03e01f807f85 0x64b3e07c03f00ff0

def z1083 : W := mkw 0x0b221b6da336f7ee 0x2164436db466defd 0xfde6bbffe7767fff 0x7fbcd77ffceecfff

def z1084 : W := mkw 0x0a221b6d83367766 0x2144436db066ceec 0xbda6ba7d877667e7 0x77b4d74fb0eeccfc

def z1085 : W := mkw 0xc81ff7fb55805500 0xf903feff6ab00aa0 0xffdfffffe7807f85 0x1ffbfffffcf00ff0

def z1086 : W := mkw 0xe01ff7fb48480000 0xfc03feff69090000 0xfffffffff878007e 0xffffffffff0f000f

def z1087 : W := mkw 0xe41ff7fb48480810 0xfc83feff69090102 0xfffffffff878181a 0xffffffffff0f0303

def z1088 : W := mkw 0x30152c001eed0000 0x4602a58003dda000 0x14273c0007ff8003 0x0284e78000fff000

def z1089 : W := mkw 0x00021a4902240000 0x2000434920448000 0x1da6ba1c07760003 0x63b4d74380eec000

def z1090 : W := mkw 0xc01713fb40000000 0x3802e27f68000000 0xff9fbbffe0000000 0x1ff3f77ffc000000

def z1091 : W := mkw 0x0815012015805500 0x0102a02402b00aa0 0x63d903a01f807f85 0xec7b207403f00ff0

def z1092 : W := mkw 0x4817276055805500 0x6902e4ec0ab00aa0 0x67df07e07f807f85 0xecfbe0fc0ff00ff0

def z1093 : W := mkw 0x03221a4da336e6ee 0x20644349b466dcdd 0xffffffffffffffff 0xffffffffffffffff

def z1094 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0xeff8c3de18787e7f 0xfdff187bc30f0fcf

def z1095 : W := mkw 0x0320180da236a2ee 0x00640301b446d45d 0xffe7fc7fe7ff87ff 0xfffcff8ffcfff0ff

def z1096 : W := mkw 0x0a221a4d83367766 0x21444349b066ceec 0xbde6ba5d87767fe7 0x77bcd74bb0eecffc

def z1097 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x7fbfff801fff8003 0xeff7fff003fff000

def z1098 : W := mkw 0x101dec0016a50000 0xc203bd8002d4a000 0x1fbffc0007f78003 0x63f7ff8000fef000

def z1099 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xbd9fbffde0000000 0x17b3f7ffbc000000

def z1100 : W := mkw 0x0815012015805500 0x0102a02402b00aa0 0x66d901e01f807f85 0xecdb203c03f00ff0

def z1101 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0xebf8c3fe18787ffe 0xfd7f187fc30f0fff

def z1102 : W := mkw 0xc000109b40000000 0x1800021368000000 0x9800b81fe0000000 0x13001703fc000000

def z1103 : W := mkw 0x801de49200000000 0xd003bc9240000000 0xff9fffffe0000000 0x1ff3fffffc000000

def z1104 : W := mkw 0xf11de5b27cc98088 0xde23bcb64f993011 0x425945a278898198 0x884b28b44f113033

def z1105 : W := mkw 0xc81ff7fb54801100 0xf903feff6a900220 0xff9fffffe0800180 0x1ff3fffffc100030

def z1106 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xffdfffffe000007c 0x1ffbfffffc00000f

def z1107 : W := mkw 0x0a221b6d83367766 0x2144436db066ceec 0xffe7bbfd87f67fe7 0xfffcf77fb0fecffc

def z1108 : W := mkw 0xc41ff7fb40000810 0xf883feff68000102 0xffdfffffe0001818 0x1ffbfffffc000303

def z1109 : W := mkw 0x381ded201eed1100 0xc703bda403dda220 0x7fffffa01ffff987 0xeffffff403ffff30

def z1110 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xffdffffff8001800 0x9ffbffffff000300

def z1111 : W := mkw 0x02221a4d03346442 0x20444349a0668c88 0x0126ba1c07706605 0x6024d74380ee0cc0

def z1112 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0xa9b8c39e1878787e 0x75371873c30f0f0f

def z1113 : W := mkw 0xc008f49b40000000 0xd8011e9368000000 0x9e81fc1fe08f8003 0xb3d03f83fc11f000

def z1114 : W := mkw 0xc81737fb55805500 0x7902e6ff6ab00aa0 0xf4473fffe7807f85 0x1e88e7fffcf00ff0

def z1115 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xbd9effdfe0000000 0x17b3dffbfc000000

def z1116 : W := mkw 0x02221a4d03346442 0x20444349a0668c88 0x013ebb9c1f707800 0x4027d77383ee0f00

def z1117 : W := mkw 0x03200804a236a2ee 0x006401009446d45d 0x00200000007f807a 0x00040000000ff00f

def z1118 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xbda6ba5d87766601 0x57b4d74bb0eeccc0

def z1119 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x1da7fc0007ff8003 0x63b4ff8000fff000

def z1120 : W := mkw 0xc01ff7fb54800000 0xf803feff6a900000 0xff9fffffff8f8003 0xfff3fffffff1f000

def z1121 : W := mkw 0xb01dec921eed0000 0xd603bd9243dda000 0xffbfffffffff8003 0xfff7fffffffff000

def z1122 : W := mkw 0xc81713fb55805500 0x3902e27f6ab00aa0 0xffdfbbffff807f85 0xfffbf77ffff00ff0

def z1123 : W := mkw 0x3008ec001eed0000 0xc6011d8003dda000 0x1da6fc001fff8003 0xe3b4df8003fff000

def z1124 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xff9ffffff8007800 0x5ff3ffffff000f00

def z1125 : W := mkw 0xc008f49b40000000 0xd8011e9368000000 0x8000b81fe0000000 0x10001703fc000000

def z1126 : W := mkw 0xc81ff7fb54801100 0xf903feff6a900220 0xffdffffff8807984 0xfffbffffff100f30

def z1127 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0xfbf8c79ff878787e 0xff7f18f3ff0f0f0f

def z1128 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xa9a6ba5d87706666 0x7534d74bb0ee0ccc

def z1129 : W := mkw 0xc81ff7fb55805500 0xf903feff6ab00aa0 0xff9fffffff807f81 0x5ff3fffffff00ff0

def z1130 : W := mkw 0xf01de5b25cc90000 0xde03bcb64b992000 0x421945a278000000 0x084328b44f000000

def z1131 : W := mkw 0xc81ff7fb55805500 0xf903feff6ab00aa0 0x151fbffdff807f81 0x42a3f7ffbff00ff0

def z1132 : W := mkw 0x0322124da112e6ee 0x20644249b4225cdd 0xa040025d800067fc 0x1408004bb0000cff

def z1133 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x665f03e01f807f85 0x8ccbe07c03f00ff0

def z1134 : W := mkw 0xc00212db40000000 0x3800425b68000000 0xbd86ba5fe0000000 0x17b0d74bfc000000

def z1135 : W := mkw 0xb41dec921eed0810 0xd683bd9243dda102 0x1fbffc021fff801b 0xe3f7ff8043fff003

def z1136 : W := mkw 0x02221a4d03346442 0x20444349a0668c88 0x09a6ba1c07706002 0x6134d74380ee0c00

def z1137 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0xe278439e1878787e 0xfc4f0873c30f0f0f

def z1138 : W := mkw 0x0a221b6d03347542 0x2144436da0668ea8 0x6166bbfc07707f84 0x4c2cd77f80ee0ff0

def z1139 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x7fdfbbe01f807f85 0xeffbf77c03f00ff0

def z1140 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x079f03e01f807f81 0xe0f3e07c03f00ff0

def z1141 : W := mkw 0x0817276015805500 0x6102e4ec02b00aa0 0x77df3fe01f807f85 0xeefbe7fc03f00ff0

def z1142 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x67df47e27f807f85 0xecfbe8fc4ff00ff0

def z1143 : W := mkw 0xc00af7fb40000000 0xf8015eff68000000 0x9800ff9fe0000000 0x13001ff3fc000000

def z1144 : W := mkw 0x0802036001005500 0x2100406c00200aa0 0x67de03e01f007f85 0xecfbc07c03e00ff0

def z1145 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0x0138839c1878787a 0x40271073830f0f0f

def z1146 : W := mkw 0xc008f49b40000000 0xd8011e9368000000 0x9918ff9fe0000000 0x13231ff3fc000000

def z1147 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x5fbffc227fff8003 0xebf7ff844ffff000

def z1148 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0x779fbffde0000000 0x0ef3f7ffbc000000

def z1149 : W := mkw 0x03221a4da336e6ee 0x20644349b466dcdd 0xffe7ba7d87ffe7ff 0xfffcf74fb0fffcff

def z1150 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0x9d1fffffe0000000 0x13a3fffffc000000

def z1151 : W := mkw 0xc81ff7fb55805500 0xf903feff6ab00aa0 0xffdfffffff007804 0xfffbffffffe00f00

def z1152 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0xefdf03e01f807fe7 0xfdfbe07c03f00ffc

def z1153 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x17bfbc001ff78001 0xe2f7f78003fef000

def z1154 : W := mkw 0xc008f49b40000000 0xd8011e9368000000 0xfa80fc1fe0000000 0x1f501f83fc000000

def z1155 : W := mkw 0x0000180902240000 0x0000030120448000 0x9da6b81d87760003 0x73b4d703b0eec000

def z1156 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0xcb78c39e1878787a 0xd96f1873c30f0f0f

def z1157 : W := mkw 0xb51de4923cc98898 0xd6a3bc9247993113 0x425945a278899998 0x884b28b44f113333

def z1158 : W := mkw 0xc00213fb40000000 0x3800427f68000000 0xf800bbffe0000000 0x1f00177ffc000000

def z1159 : W := mkw 0xc008f49b40000000 0xd8011e9368000000 0x1000bc1de0000000 0x02001783bc000000

def z1160 : W := mkw 0x4017376940000000 0x6802e6ed28000000 0x9c07bc7de0000000 0x1380f78fbc000000

def z1161 : W := mkw 0x1817276015815500 0x6302e4ec02b02aa0 0x67df07e01f81ff85 0xecfbe0fc03f03ff0

def z1162 : W := mkw 0xc01df49b54800000 0xd803be936a900000 0x9f9ffc1fff800001 0xf3f3ff83fff00000

def z1163 : W := mkw 0x03221a4d2334e4ca 0x20644349a4669c99 0x4367fe3e67f9e198 0xc86cffc7ccff3c33

def z1164 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xfe87fc7fe0000000 0x1fd0ff8ffc000000

def z1165 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0xe7df03e21f807ffd 0xfcfbe07c43f00fff

def z1166 : W := mkw 0xf01ff7fb5cc90000 0xfe03feff6b992000 0xffbffffff8f98002 0xfff7ffffff1f3000

def z1167 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0x1407bc7de0000000 0x0280f78fbc000000

def z1168 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x67df03e01f887fff 0xecfbe07c03f10fff

def z1169 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x7fdf03e01f867f87 0xeffbe07c03f0cff0

def z1170 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xffdfffffe0080018 0x9ffbfffffc010003

def z1171 : W := mkw 0xc01df49b40000000 0xd803be9368000000 0xff9ffc7fe0000000 0x1ff3ff8ffc000000

def z1172 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xff9fffffe0800781 0x1ff3fffffc1000f0

def z1173 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0xfff9c7fff8f87fff 0xffff38ffff1f0fff

def z1174 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x1fbffc001ff78001 0x43f7ff8003fef000

def z1175 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x163f7c001fff8003 0xe2c7ef8003fff000

def z1176 : W := mkw 0xf81de5b25cc91100 0xdf03bcb64b992220 0x425945a278899980 0x884b28b44f113330

def z1177 : W := mkw 0xb01dec921eed0000 0xd603bd9243dda000 0xffffff9e1ffff807 0xfffffff3c3ffff00

def z1178 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x63de03801f807f85 0xec7bc07003f00ff0

def z1179 : W := mkw 0xc80af7fb41005500 0xf9015eff68200aa0 0xf840ffffe0007f84 0x1f081ffffc000ff0

def z1180 : W := mkw 0xc81ff7fb55805500 0xf903feff6ab00aa0 0x77dfbffdff807f85 0xeefbf7ffbff00ff0

def z1181 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x635f03e01f807f84 0xcc6be07c03f00ff0

def z1182 : W := mkw 0x0000080402342040 0x0000010080468408 0x9da6b81c07760063 0x73b4d70380eec00c

def z1183 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0xffbffc021fff8003 0xfff7ff8043fff000

def z1184 : W := mkw 0x02221a4d03346442 0x20444349a0668c88 0xebe6fa1e0778607e 0xfd7cdf43c0ef0c0f

def z1185 : W := mkw 0xc81ff7fb55805500 0xf903feff6ab00aa0 0x991eff9fff007800 0x5323dff3ffe00f00

def z1186 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xe31fffffe0000000 0x1c63fffffc000000

def z1187 : W := mkw 0xd01ff7fb54810000 0xfa03feff6a902000 0xff9fffffe0818000 0x1ff3fffffc103000

def z1188 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0xbfbffe1c1fff8003 0xf7f7ffc383fff000

def z1189 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x1427bc0007f78001 0x0284f78000fef000

def z1190 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x1dbefc001f7f8003 0x63b7df8003eff000

def z1191 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x1ffffc001fff807f 0xe3ffff8003fff00f

def z1192 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xffdfffffe0000004 0xbffbfffffc000000

def z1193 : W := mkw 0xc008f49b40000000 0xd8011e9368000000 0xda01fc3fe0000000 0x1b403f87fc000000

def z1194 : W := mkw 0x03221a4da336e6ee 0x20644349b466dcdd 0x9926fe1fe77fe07a 0x5324dfc3fceffc0f

def z1195 : W := mkw 0x03221a4da336e6ee 0x20644349b466dcdd 0x9c27fc7fe7ff87fb 0x1384ff8ffcfff0ff

def z1196 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0x571fffffe0000000 0x0ae3fffffc000000

def z1197 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x67df03e01f007f84 0x4cfbe07c03e00ff0

def z1198 : W := mkw 0xc01ff7fb41004400 0xf803feff68200880 0xff9fffffe7000601 0x1ff3fffffce000c0

def z1199 : W := mkw 0xc81ff7fb55805500 0xf903feff6ab00aa0 0xffdfffffe7800785 0xbffbfffffcf000f0

def z1200 : W := mkw 0x00021a4d02342040 0x20004349a0468408 0xbda6ba5d87766067 0x77b4d74bb0eecc0c

def z1201 : W := mkw 0x03221a4da336e6ee 0x20644349b466dcdd 0xffe7ba7fe7f667ff 0xfffcf74ffcfeccff

def z1202 : W := mkw 0x01000000a00282ac 0x0020000014005055 0xffc1c67fe08f87ff 0xbff838cffc11f0ff

def z1203 : W := mkw 0x0015080016a40000 0x0002a10002d48000 0x1fbffc001fff8003 0xe3f7ff8003fff000

def z1204 : W := mkw 0x02221a4d03346442 0x20444349a0668c88 0x0026b81c07700000 0x0004d70380ee0000

def z1205 : W := mkw 0x03221a4da336e6ee 0x20644349b466dcdd 0xfde6ba7fe7ffe7ff 0xffbcd74ffcfffcff

def z1206 : W := mkw 0xf81ff7fb5cc91100 0xff03feff6b992220 0xffdffffff8899980 0x9ffbffffff113330

def z1207 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x193efc001fff8003 0xe327df8003fff000

def z1208 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xbfa6fa5d877e6667 0xf7f4df4bb0efcccc

def z1209 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x1e3ffc001fff8003 0x83c7ff8003fff000

def z1210 : W := mkw 0xc81ff7fb55805500 0xf903feff6ab00aa0 0xff9fffffe7806785 0x7ff3fffffcf00cf0

def z1211 : W := mkw 0xc01ff7fb41004400 0xf803feff68200880 0xffdfffffff007e05 0xfffbffffffe00fc0

def z1212 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x0bbef8001fff8003 0xe177df0003fff000

def z1213 : W := mkw 0x01000000a00282ac 0x0020000014005055 0xffd94463f88f87ff 0xfffb288c7f11f0ff

def z1214 : W := mkw 0x0220180d82362266 0x00440301b046c44c 0x9c26b81d87760063 0x1384d703b0eec00c

def z1215 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xb526ba5d87766665 0x56a4d74bb0eecccc

def z1216 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0xffdf47e3ff8fff87 0xfffbe8fc7ff1fff0

def z1217 : W := mkw 0x03221a4da336e6ee 0x20644349b466dcdd 0xbda6ba5d877fe67f 0x77b4d74bb0effccf

def z1218 : W := mkw 0x0320180da236a2ee 0x00640301b446d45d 0x9fa7fc1fe7ff807b 0xf3f4ff83fcfff00f

def z1219 : W := mkw 0x03221a4da336e6ee 0x20644349b466dcdd 0xffe6fa5f87ffe7ff 0xfffcdf4bf0fffcff

def z1220 : W := mkw 0x01000000a00282ac 0x0020000014005055 0xe2414463e08f87ff 0xbc48288c7c11f0ff

def z1221 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x055f03e01f807f85 0xe0abe07c03f00ff0

def z1222 : W := mkw 0x0002024001004400 0x2000404800200880 0x67df03e01f807f85 0xecfbe07c03f00ff0

def z1223 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0xebb8c39e1878787a 0x5d771873c30f0f0f

def z1224 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0x63f8839c1878787e 0xec7f1073830f0f0f

def z1225 : W := mkw 0xec1ff7fb5cc81910 0xfd83feff6b990322 0xffdffffff8881998 0x9ffbffffff110333

def z1226 : W := mkw 0x02221a4d03346442 0x20444349a0668c88 0x1526ba1c07766001 0x42a4d74380eecc00

def z1227 : W := mkw 0xc008f49b40000000 0xd8011e9368000000 0xf800fc7fe0000000 0x1f001f8ffc000000

def z1228 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xbc26ba5d87766667 0x1784d74bb0eecccc

def z1229 : W := mkw 0x2400000408582850 0x04800000810b050a 0xebf8839c1878787e 0xfd7f1073830f0f0f

def z1230 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xff9ffffff8000000 0xfff3ffffff000000

def z1231 : W := mkw 0x03221a4da336e6ee 0x20644349b466dcdd 0xbfa7fe5fe7ffe67f 0xf7f4ffcbfcfffccf

def z1232 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xffa6fa5f87766667 0x7ff4df4bf0eecccc

def z1233 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0xeff9c39e18f8787f 0xfdff3873c31f0f0f

def z1234 : W := mkw 0x02221a4d03346442 0x20444349a0668c88 0x0126ba1c07706066 0x6024d74380ee0c0c

def z1235 : W := mkw 0xc01ff7fb54800000 0xf803feff6a900000 0xff9fffffff000000 0x5ff3ffffffe00000

def z1236 : W := mkw 0xc81ff7fb55805500 0xf903feff6ab00aa0 0xffdfffffff8fff87 0xfffbfffffff1fff0

def z1237 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x153fbc001fff8003 0xe2a7f78003fff000

def z1238 : W := mkw 0x01000000a00282ac 0x0020000014005055 0xfec14463f88fffff 0xffd8288c7f11ffff

def z1239 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xffa7ba7d87766667 0x7ff4f74fb0eecccc

def z1240 : W := mkw 0x0817136915805500 0x2102e26d22b00aa0 0xe7df03fd9f807f85 0xfcfbe07fb3f00ff0

def z1241 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xe79fbbffe0000000 0x1cf3f77ffc000000

def z1242 : W := mkw 0xc81ff7fb55805500 0xf903feff6ab00aa0 0xff9fffffff800781 0xfff3fffffff000f0

def z1243 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x67df43e21f887f9d 0xecfbe87c43f10ff3

def z1244 : W := mkw 0x0a221b6d83367766 0x2144436db066ceec 0xbda6bbdd87767e67 0x77b4d77bb0eecfcc

def z1245 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0xebf9c3be18f879fe 0xfd7f3877c31f0f3f

def z1246 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xbda6ba5d87766062 0x57b4d74bb0eecc0c

def z1247 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x07bfb8001fff8003 0xe0f7f70003fff000

def z1248 : W := mkw 0x1000080016a50000 0x0200010002d4a000 0x1da6b80007f78003 0x63b4d70000fef000

def z1249 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xffe6ba5d87766667 0xfffcd74bb0eecccc

def z1250 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0xfff9c7fff8fff87f 0xffff38ffff1fff0f

def z1251 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0xfbf8c79e187ff87e 0xff7f18f3c30fff0f

def z1252 : W := mkw 0xc81df5bb54801100 0xd903beb76a900220 0xda59fdbff8801980 0x9b4b3fb7ff100330

def z1253 : W := mkw 0x301dec000a6d0000 0xc603bd80014da000 0x1fbffc00077f8003 0x63f7ff8000eff000

def z1254 : W := mkw 0xc01df49b40000000 0xd803be9368000000 0x9a19fc1fe0000000 0x13433f83fc000000

def z1255 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x679f03e01f807f81 0x4cf3e07c03f00ff0

def z1256 : W := mkw 0x3008ec000a6d0000 0xc6011d80014da000 0x1fbefc001f7f8003 0xe3f7df8003eff000

def z1257 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xffa7fe7fe7ffe667 0xfff4ffcffcfffccc

def z1258 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xffdffffff8807f85 0xfffbffffff100ff0

def z1259 : W := mkw 0x03221a4da336e6ee 0x20644349b466dcdd 0xe166ba7fe77067fc 0x5c2cd74ffcee0cff

def z1260 : W := mkw 0xc81ff7fb55805500 0xf903feff6ab00aa0 0xe7dfbbffff807f85 0xfcfbf77ffff00ff0

def z1261 : W := mkw 0xec1de5b25cc81910 0xdd83bcb64b990322 0x425945a278881998 0x884b28b44f110333

def z1262 : W := mkw 0x381ded201eed1100 0xc703bda403dda220 0x1fbffc201fff8183 0xe3f7ff8403fff030

def z1263 : W := mkw 0xb41de4921cc90810 0xd683bc9243992102 0xfed94582188f987f 0xbfdb28b04311f30f

def z1264 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x63de03e01f007f84 0xec7bc07c03e00ff0

def z1265 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x1bbefc001f7f8002 0xe377df8003eff000

def z1266 : W := mkw 0x01000000a00282ac 0x0020000014005055 0xffe1c463e0ff87ff 0xfffc388c7c1ff0ff

def z1267 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xffe7fe7d87ffe7e7 0xfffcffcfb0fffcfc

def z1268 : W := mkw 0x0000100900000000 0x0000020120000000 0x9800fc1fe0000000 0x13001f83fc000000

def z1269 : W := mkw 0x03221a4da336e6ee 0x20644349b466dcdd 0xbda6ba5fe776667f 0x77b4d74bfceecccf

def z1270 : W := mkw 0x01000000a00282ac 0x0020000014005055 0xfe814463e08f87fb 0x1fd0288c7c11f0ff

def z1271 : W := mkw 0xb408e49608592850 0xd6811c92c10b250a 0xebf8c79e1879f87e 0xfd7f18f3c30f3f0f

def z1272 : W := mkw 0xc01ff7fb54800000 0xf803feff6a900000 0xff9ffffff8800000 0x9ff3ffffff100000

def z1273 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xff9fffffe0006004 0x7ff3fffffc000c00

def z1274 : W := mkw 0x301ded201eed0000 0xc603bda403dda000 0x5fbffda01fff8003 0xebf7ffb403fff000

def z1275 : W := mkw 0x0000080002240000 0x0000010000448000 0xbda6ba1c07760003 0x77b4d74380eec000

def z1276 : W := mkw 0xc01ff6db40000000 0xf803fedb68000000 0xbf9ffe5fe0000000 0x17f3ffcbfc000000

def z1277 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xff9fffffe0060003 0x3ff3fffffc00c000

def z1278 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xbca6b85d87760667 0x3794d70bb0eec0cc

def z1279 : W := mkw 0x03221a4da336e6ee 0x20644349b466dcdd 0xbde6ba5d877667ff 0x77bcd74bb0eeccff

def z1280 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xff9fffffe008007a 0x1ff3fffffc01000f

def z1281 : W := mkw 0x01000000a00282ac 0x0020000014005055 0xffc14663e08fe7ff 0xfff828cc7c11fcff

def z1282 : W := mkw 0x3008ec000a6d0000 0xc6011d80014da000 0x1c26fc00077f8003 0x0384df8000eff000

def z1283 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0x9c26b85d87766667 0x7384d70bb0eecccc

def z1284 : W := mkw 0xc81ff7fb55805500 0xf903feff6ab00aa0 0xffdfffffff807980 0xdffbfffffff00f30

def z1285 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0xe9f8839e1870787e 0x7d3f1073c30e0f0f

def z1286 : W := mkw 0xf01ff7fb48490000 0xfe03feff69092000 0xff9fffffe0098000 0x1ff3fffffc013000

def z1287 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0xfffefb9e1878787e 0xffffdf73c30f0f0f

def z1288 : W := mkw 0x01000000a00282ac 0x0020000014005055 0x9c414463e08f87ff 0xb388288c7c11f0ff

def z1289 : W := mkw 0xf01de5b25cc90000 0xde03bcb64b992000 0xfe9945e3f88f8003 0xbfd328bc7f11f000

def z1290 : W := mkw 0xc81ff7fb54801100 0xf903feff6a900220 0xffdfffffff801981 0xfffbfffffff00330

def z1291 : W := mkw 0x4817136955805500 0x2902e26d2ab00aa0 0x67df03e1ff807f85 0xecfbe07c3ff00ff0

def z1292 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x015e03801f007f84 0x402bc07003e00ff0

def z1293 : W := mkw 0xc008f49b40000000 0xd8011e9368000000 0x9800fc1fe008007a 0x13001f83fc01000f

def z1294 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0xfff9c7fe18ffffff 0xffff38ffc31fffff

def z1295 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xfda6ba7fe7766667 0x7fb4d74ffceecccc

def z1296 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x1826fc00077f8002 0x0304df8000eff000

def z1297 : W := mkw 0xf01de5b25cc90000 0xde03bcb64b992000 0x0219458018898000 0x804328b003113000

def z1298 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x7ffffc001fff8007 0xefffff8003fff000

def z1299 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x7fdf47e01f807f85 0xeffbe8fc03f00ff0

def z1300 : W := mkw 0xc81ff7fb55805500 0xf903feff6ab00aa0 0xff9fffffff807801 0xfff3fffffff00f00

def z1301 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xffdffffff808787e 0xfffbffffff010f0f

def z1302 : W := mkw 0xf008f49b48490000 0xde011e9369092000 0x9800fc1fe0098000 0x13001f83fc013000

def z1303 : W := mkw 0x03221a4da336e6ee 0x20644349b466dcdd 0xbde6fe5fe7ffe7ff 0xf7bcdfcbfcfffcff

def z1304 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0xebf9c7be7878787e 0xfd7f38f7cf0f0f0f

def z1305 : W := mkw 0xc00af7fb40000000 0xf8015eff68000000 0xe000bbffe0000000 0x1c00177ffc000000

def z1306 : W := mkw 0xc008f49b40000000 0xd8011e9368000000 0xda18fd9fe0000000 0x1b431fb3fc000000

def z1307 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0x9826b81d87760062 0x1304d703b0eec00c

def z1308 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x3fbffe001fffe007 0xe7f7ffc003fffc00

def z1309 : W := mkw 0x0815000015805500 0x0102a00002b00aa0 0x67df03801f807f85 0xecfbe07003f00ff0

def z1310 : W := mkw 0xc01df5bb40000000 0xd803beb768000000 0xfe99fdffe0000000 0x1fd33fbffc000000

def z1311 : W := mkw 0xf81dedb25eed1100 0xdf03bdb64bdda220 0x5ffffda27fff9983 0xebffffb44ffff330

def z1312 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xffe7fe7fe77e667f 0xfffcffcffcefcccf

def z1313 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0xefdf43e21f807f85 0xfdfbe87c43f00ff0

def z1314 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xfa19ffffe0000000 0x1f433ffffc000000

def z1315 : W := mkw 0x03221a4da336e6ee 0x20644349b466dcdd 0xbde7be7de7ffe7ff 0xf7bcf7cfbcfffcff

def z1316 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xfde6ba7d877667e7 0x7fbcd74fb0eeccfc

def z1317 : W := mkw 0x02221a4d03346442 0x20444349a0668c88 0xada6ba5c07706667 0x75b4d74b80ee0ccc

def z1318 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x6fdf43e01f887f87 0xedfbe87c03f10ff0

def z1319 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xde1ffdffe0000000 0x1bc3ffbffc000000

def z1320 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xff9fffffe0000066 0x3ff3fffffc00000c

def z1321 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x1fbffc0007ff8003 0x03f7ff8000fff000

def z1322 : W := mkw 0x0b221b6da336f7ee 0x2164436db466defd 0xffe7ffffe7ffffff 0xfffcfffffcffffff

def z1323 : W := mkw 0x03221a4da336e6ee 0x20644349b466dcdd 0xbda6ba5d87f7e7e7 0x77b4d74bb0fefcfc

def z1324 : W := mkw 0x300008001eed0000 0x0600010003dda000 0x142638001fff8003 0xe284c70003fff000

def z1325 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xff9fffffe0878001 0x1ff3fffffc10f000

def z1326 : W := mkw 0xb41de4921cc90810 0xd683bc9243992102 0x4258418218081818 0x884b083043010303

def z1327 : W := mkw 0x0220180d82362266 0x00440301b046c44c 0xbda6ba1d87766067 0x77b4d743b0eecc0c

def z1328 : W := mkw 0xf81ff7fb5dc95500 0xff03feff6bb92aa0 0xffdfffffff89ff85 0xfffbfffffff13ff0

def z1329 : W := mkw 0xc01737fb40000000 0x7802e6ff68000000 0xfd87bfffe0000000 0x1fb0f7fffc000000

def z1330 : W := mkw 0x0a221b6d83367766 0x2144436db066ceec 0xfffebbfd9f767fe7 0xffffd77fb3eecffc

def z1331 : W := mkw 0x301508001eed0000 0x0602a10003dda000 0x1fbfb8001fff8003 0xe3f7f70003fff000

def z1332 : W := mkw 0x03221a4da336e6ee 0x20644349b466dcdd 0xbfe7fe5d87ffe7ff 0xf7fcffcbb0fffcff

def z1333 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xffe7fe7fe7f667e7 0xfffcffcffcfeccfc

def z1334 : W := mkw 0x0000000400102040 0x0000000080020408 0xebf8c39e1878787e 0xfd7f1873c30f0f0f

def z1335 : W := mkw 0x0802036015805500 0x2100406c02b00aa0 0x63d803e01f807f85 0xec7b007c03f00ff0

def z1336 : W := mkw 0x00021a4902240000 0x2000434920448000 0xffa7fe7fe7ff8003 0xfff4ffcffcfff000

def z1337 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xb9a6ba1d87766066 0x7734d743b0eecc0c

def z1338 : W := mkw 0x03200804a336e6ee 0x006401009466dcdd 0x00200000077fe67f 0x6004000000effccf

def z1339 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x013eb8001ff78001 0x4027d70003fef000

def z1340 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x1d3ffc001fff8003 0x43a7ff8003fff000

def z1341 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x7fbffc601fff8003 0xeff7ff8c03fff000

def z1342 : W := mkw 0xe008f49b48480000 0xdc011e9369090000 0x9bb8fc1ff8780002 0xf3771f83ff0f0000

def z1343 : W := mkw 0xc00af6db40000000 0xf8015edb68000000 0xff9effdfe0000000 0x1ff3dffbfc000000

def z1344 : W := mkw 0x02221a4d03346442 0x20444349a0668c88 0x8926ba1c07706062 0x5124d74380ee0c0c

def z1345 : W := mkw 0x03221a4da336e6ee 0x20644349b466dcdd 0xfde7be7fe7f7e7ff 0x7fbcf7cffcfefcff

def z1346 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xbfa7fe5d87766667 0x77f4ffcbb0eecccc

def z1347 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0x8138839e18707878 0x50271073c30e0f0f

def z1348 : W := mkw 0xc008f49b40000000 0xd8011e9368000000 0xfac0fc1fe008007e 0xbf581f83fc01000f

def z1349 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x5ffffc201fff8183 0xebffff8403fff030

def z1350 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x655f03e01f807f85 0x4cabe07c03f00ff0

def z1351 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x77df07e1ff807f85 0xeefbe0fc3ff00ff0

def z1352 : W := mkw 0xf41de5b25cc90810 0xde83bcb64b992102 0x425945a278899818 0x884b28b44f113303

def z1353 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x1dbfbc001ff78003 0x63b7f78003fef000

def z1354 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xbda6fe5d877fe667 0x77b4dfcbb0effccc

def z1355 : W := mkw 0xb41de4921cc90810 0xd683bc9243992102 0x0219458018899800 0x804328b003113300

def z1356 : W := mkw 0x0002124d01106440 0x20004249a0220c88 0xbda6ba5d87706667 0x77b4d74bb0ee0ccc

def z1357 : W := mkw 0x01021a49a22682ac 0x202043493444d055 0xffe7fe7fe7ff87ff 0xfffcffcffcfff0ff

def z1358 : W := mkw 0xc008f49b40000000 0xd8011e9368000000 0xbc80fc5fe0000000 0x17901f8bfc000000

def z1359 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xff9fffffe00f8002 0x1ff3fffffc01f000

def z1360 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0xebf8c39e18f87fff 0xfd7f1873c31f0fff

def z1361 : W := mkw 0x301dec001eed0000 0xc603bd8003dda000 0x1fbfff801ffff803 0xe3f7fff003ffff00

def z1362 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0xbda6ba5d87706664 0x57b4d74bb0ee0ccc

def z1363 : W := mkw 0xc00af6db40000000 0xf8015edb68000000 0xb800fe5fe0000000 0x17001fcbfc000000

def z1364 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0xe7df03e3ff807f85 0xfcfbe07c7ff00ff0

def z1365 : W := mkw 0xc00af6db40000000 0xf8015edb68000000 0x9c06fc5fe0000000 0x1380df8bfc000000

def z1366 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0xffdfffffe08807ff 0xbffbfffffc1100ff

def z1367 : W := mkw 0xc008f49b40000000 0xd8011e9368000000 0x9b98fc1fe0000000 0x13731f83fc000000

def z1368 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0x8bb8c39e1878787a 0xf1771873c30f0f0f

def z1369 : W := mkw 0x4017376940000000 0x6802e6ed28000000 0xb4073e7de0000000 0x1680e7cfbc000000

def z1370 : W := mkw 0xc01ff7fb40000000 0xf803feff68000000 0x9f9ffc7fe0000000 0x13f3ff8ffc000000

def z1371 : W := mkw 0x0817036015805500 0x2102e06c02b00aa0 0x011e03801f807f81 0x4023c07003f00ff0

def z1372 : W := mkw 0xc008f49b40000000 0xd8011e9368000000 0x9800fc1fe00f8002 0x13001f83fc01f000

def z1373 : W := mkw 0x01000000a00282ac 0x0020000014005055 0xffc74463e78f87ff 0xfff8e88c7cf1f0ff

def z1374 : W := mkw 0x02221a4d03346442 0x20444349a0668c88 0x25a6ba5c07706000 0x44b4d74b80ee0c00

def z1375 : W := mkw 0x02221a4d03346442 0x20444349a0668c88 0x1da6ba1c07706000 0x43b4d74380ee0c00

def z1376 : W := mkw 0x0220180d82362266 0x00440301b046c44c 0xbda6b85d87760667 0x77b4d70bb0eec0cc

def z1377 : W := mkw 0x00021a4982260224 0x200043493044c044 0xbda6ba5d87760667 0x77b4d74bb0eec0cc

def z1378 : W := mkw 0x0220080483366666 0x004401009066cccc 0xbda6ba1c07766667 0x77b4d74380eecccc

def z1379 : W := mkw 0x0000080402342040 0x0000010080468408 0x1da6ba1c07766003 0x63b4d74380eecc00

def z1380 : W := mkw 0xc01737fb40000000 0x7802e6ff68000000 0xf79f3fffe0000000 0x1ef3e7fffc000000

def z1381 : W := mkw 0x02221a4d03346442 0x20444349a0668c88 0x1526ba5d87706000 0x42a4d74bb0ee0c00

def z1382 : W := mkw 0xc00af7fb40000000 0xf8015eff68000000 0xfe81ffffe0000000 0x1fd03ffffc000000

def z1383 : W := mkw 0xa408c09608582850 0x94811812c10b050a 0xe3f8839e1870787c 0xfc7f1073c30e0f0f

def z1384 : W := mkw 0x01000000a00282ac 0x0020000014005055 0x56414463e08f87ff 0xaac8288c7c11f0ff

def z1385 : W := mkw 0xc008f49b40000000 0xd8011e9368000000 0xff99ffffe0000000 0x1ff33ffffc000000

def z1386 : W := mkw 0x0220180d02342042 0x00440301a0468408 0x1da6b81c07760003 0x63b4d70380eec000

def z1387 : W := mkw 0x02221a4d83366666 0x20444349b066cccc 0x0126ba1c07766601 0x4024d74380eeccc0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z7,z8]),(1,[z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z10,z11,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z12,z13]),(0,[z14,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z15,z16,z5,z8])],[(1,[z17,z1,z18,z3,z5,z8]),(0,[z1,z2,z3,z4,z5,z19,z8]),(0,[z1,z2,z3,z3,z4,z5,z8]),(0,[z20,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z21,z3,z4,z5,z8]),(0,[z1,z2,z3,z5,z22,z8,z23])],[(0,[z1,z24,z2,z3,z4,z5,z25]),(1,[z0,z2,z26,z4,z5,z8]),(0,[z1,z2,z3,z4,z27,z28,z8]),(0,[z1,z2,z3,z4,z5,z29,z8]),(0,[z30,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z31,z4,z5,z32]),(0,[z1,z2,z33,z3,z4,z5,z8])],[(1,[z1,z2,z3,z4,z34,z8]),(0,[z1,z2,z3,z4,z5,z8,z8]),(0,[z1,z2,z3,z4,z35,z5,z8])],[(0,[z1,z18,z3,z36,z4,z5,z8]),(0,[z37,z1,z18,z3,z4,z5,z8]),(0,[z1,z24,z38,z3,z4,z5,z8]),(0,[z1,z2,z11,z3,z4,z5,z12]),(1,[z39,z2,z3,z4,z5,z8])],[(0,[z1,z40,z24,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z41]),(0,[z1,z42,z3,z43,z4,z5,z8]),(0,[z44,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z45,z28,z8]),(0,[z1,z2,z11,z4,z5,z8,z12]),(0,[z1,z46,z3,z43,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z47]),(1,[z1,z48,z3,z4,z5,z8]),(0,[z1,z2,z3,z49,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z8,z50]),(0,[z51,z1,z2,z3,z4,z5,z8]),(0,[z0,z1,z2,z3,z4,z5,z52]),(0,[z53,z54,z1,z2,z3,z5,z8]),(0,[z1,z2,z3,z55,z4,z5,z8]),(0,[z1,z2,z56,z3,z57,z5,z8]),(0,[z1,z2,z3,z58,z4,z5,z8]),(0,[z1,z2,z3,z59,z4,z5,z60]),(1,[z61,z1,z3,z4,z5,z8]),(0,[z1,z2,z3,z62,z63,z5,z8])]],
   [[(0,[z64,z1,z2,z3,z4,z5,z25]),(0,[z65,z1,z2,z3,z4,z5,z12]),(0,[z1,z2,z3,z66,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z67])],[(0,[z1,z68,z18,z3,z4,z5,z8]),(0,[z69,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z25,z70]),(0,[z1,z2,z3,z71,z4,z5,z8])],[(0,[z72,z1,z24,z3,z4,z5,z8]),(0,[z73,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z74]),(0,[z1,z2,z3,z3,z4,z5,z25])],[(1,[z1,z75,z3,z4,z5,z8])],[(0,[z76,z1,z18,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z77,z8]),(0,[z1,z2,z3,z4,z5,z8,z78]),(0,[z1,z79,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z35,z5,z25]),(0,[z1,z2,z3,z80,z4,z5,z8])],[(0,[z1,z18,z3,z4,z81,z5,z8]),(0,[z1,z2,z3,z4,z82,z5,z8]),(1,[z83,z1,z3,z4,z5,z8]),(0,[z1,z2,z3,z84,z4,z5,z8])],[(0,[z1,z2,z3,z4,z85,z5,z8]),(0,[z1,z24,z11,z3,z4,z5,z8]),(0,[z1,z24,z2,z3,z4,z5,z12]),(0,[z1,z2,z3,z43,z4,z5,z47]),(0,[z1,z2,z3,z4,z86,z5,z8]),(0,[z87,z1,z2,z3,z4,z5,z8])],[(0,[z53,z1,z88,z3,z4,z5,z8]),(1,[z37,z2,z3,z4,z45,z8]),(0,[z1,z2,z3,z4,z89,z5,z8]),(0,[z90,z1,z2,z3,z91,z5,z8]),(0,[z1,z46,z2,z3,z57,z5,z8]),(0,[z1,z2,z3,z4,z92,z5,z8])]],
   [[(0,[z1,z2,z93,z3,z4,z5,z8]),(0,[z1,z2,z94,z3,z4,z5,z8]),(0,[z1,z2,z11,z3,z4,z5,z29]),(0,[z1,z2,z3,z59,z4,z28,z8]),(0,[z1,z95,z2,z3,z4,z5,z8])],[(0,[z1,z24,z3,z4,z5,z8,z70]),(0,[z1,z2,z3,z96,z4,z5,z8]),(0,[z1,z2,z3,z97,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z98]),(0,[z1,z2,z3,z4,z99,z5,z8]),(0,[z1,z2,z3,z100,z4,z5,z8])],[(0,[z69,z1,z2,z3,z4,z5,z25]),(0,[z1,z2,z3,z4,z5,z25,z22]),(0,[z1,z2,z101,z3,z4,z5,z8]),(0,[z1,z2,z3,z102,z4,z5,z103]),(0,[z1,z2,z3,z4,z104,z5,z8])],[(0,[z105,z1,z2,z18,z3,z4,z5]),(0,[z1,z24,z3,z4,z106,z5,z8]),(0,[z53,z1,z2,z3,z106,z5,z8]),(0,[z107,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z108,z4,z5,z8]),(0,[z109,z110,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z111]),(0,[z1,z2,z3,z4,z112,z5,z8])],[(0,[z1,z2,z113,z3,z4,z5,z8]),(0,[z64,z1,z2,z3,z4,z5,z12]),(0,[z114,z1,z2,z3,z4,z5,z8]),(0,[z115,z1,z2,z3,z4,z5,z8]),(0,[z116,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z62,z4,z63,z8])],[(0,[z54,z1,z24,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z117,z5,z8]),(0,[z14,z1,z2,z3,z4,z5,z12])],[(0,[z1,z2,z3,z4,z5,z118,z8]),(0,[z119,z1,z2,z26,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z120,z8]),(1,[z1,z121,z3,z4,z5,z22]),(0,[z1,z2,z3,z3,z4,z5,z12])],[(0,[z122,z1,z18,z3,z4,z5,z8]),(0,[z1,z42,z3,z4,z5,z123,z8]),(0,[z124,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z125]),(0,[z1,z2,z3,z59,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z126,z8])]],
   [[(1,[z1,z2,z3,z4,z5,z8]),(0,[z1,z18,z3,z4,z127,z5,z8]),(0,[z53,z1,z24,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z128,z5,z8]),(1,[z1,z2,z129,z4,z5,z12]),(0,[z130,z1,z2,z3,z4,z5,z131]),(0,[z1,z132,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z12]),(0,[z1,z2,z3,z4,z133,z5,z8]),(0,[z1,z2,z134,z3,z4,z5,z8])],[(0,[z1,z2,z68,z3,z4,z5,z8]),(0,[z1,z2,z3,z135,z4,z5,z8]),(0,[z1,z2,z136,z3,z4,z5,z8]),(0,[z72,z1,z2,z3,z4,z5,z137]),(0,[z1,z2,z3,z138,z4,z5,z8]),(0,[z1,z2,z3,z4,z139,z5,z8])],[(0,[z64,z1,z18,z3,z4,z5,z8]),(0,[z1,z18,z3,z102,z4,z5,z8]),(0,[z1,z2,z3,z4,z140,z5,z70]),(1,[z1,z2,z3,z141,z5,z8]),(0,[z109,z1,z2,z3,z4,z142,z8])],[(0,[z1,z18,z3,z4,z63,z5,z8]),(0,[z1,z143,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z144,z8]),(0,[z1,z2,z3,z4,z145,z5,z8]),(0,[z1,z2,z146,z3,z4,z5,z8]),(0,[z1,z2,z3,z147,z4,z5,z8])],[(0,[z17,z1,z2,z18,z3,z5,z8]),(0,[z1,z2,z3,z4,z148,z5,z8]),(0,[z1,z2,z149,z3,z4,z5,z8])],[(1,[z1,z150,z3,z4,z5,z8]),(0,[z1,z2,z56,z129,z4,z5,z8]),(0,[z1,z2,z3,z36,z5,z28,z8]),(0,[z151,z1,z2,z3,z4,z5,z8]),(0,[z1,z3,z4,z5,z22,z8,z137]),(0,[z1,z2,z3,z4,z5,z12,z12]),(0,[z115,z1,z2,z3,z4,z5,z25])],[(0,[z1,z18,z3,z4,z5,z28,z8]),(0,[z152,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z153,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z154,z8]),(0,[z69,z1,z2,z3,z4,z5,z12]),(0,[z1,z2,z3,z4,z155,z5,z8]),(0,[z1,z3,z43,z4,z5,z22,z8]),(0,[z1,z2,z3,z156,z4,z5,z8]),(0,[z1,z2,z157,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z158,z8])],[(0,[z1,z2,z68,z18,z3,z5,z8]),(1,[z1,z2,z3,z159,z5,z8]),(0,[z1,z2,z26,z4,z160,z5,z8]),(1,[z1,z161,z3,z4,z5,z8]),(0,[z90,z1,z162,z3,z4,z5,z8]),(0,[z163,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z164,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z74])]],
   [[(0,[z1,z18,z3,z31,z4,z5,z8]),(0,[z1,z24,z3,z4,z5,z19,z8]),(0,[z1,z2,z3,z4,z165,z5,z8]),(0,[z1,z2,z3,z4,z5,z166,z8]),(0,[z1,z2,z3,z43,z4,z5,z8]),(0,[z1,z167,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z59,z4,z5,z25]),(0,[z1,z2,z3,z4,z5,z8,z168]),(0,[z1,z2,z3,z4,z5,z8,z169])],[(1,[z1,z170,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z171,z5,z8])],[(0,[z1,z2,z3,z4,z5,z172,z8]),(0,[z72,z1,z121,z3,z4,z5,z8]),(1,[z1,z173,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z174])],[(0,[z1,z2,z3,z4,z175,z5,z8]),(0,[z1,z11,z3,z176,z4,z5,z8]),(1,[z1,z2,z177,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z25,z178])],[(0,[z65,z1,z24,z3,z4,z5,z8]),(0,[z1,z46,z2,z3,z179,z5,z8]),(0,[z180,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z62,z5,z8,z103]),(0,[z1,z181,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z182,z8]),(0,[z1,z183,z2,z3,z4,z5,z8]),(0,[z184,z1,z2,z3,z4,z5,z8])],[(0,[z1,z18,z3,z185,z4,z5,z8]),(0,[z186,z1,z2,z3,z4,z5,z8])],[(0,[z187,z1,z18,z3,z4,z5,z8]),(0,[z1,z24,z3,z36,z4,z5,z8]),(0,[z37,z1,z2,z3,z188,z5,z8]),(0,[z1,z2,z3,z189,z4,z5,z8]),(0,[z190,z1,z2,z3,z4,z5,z8]),(0,[z191,z1,z2,z3,z57,z5,z8]),(0,[z1,z2,z3,z102,z4,z5,z25])],[(0,[z1,z1,z24,z3,z4,z5,z8]),(0,[z1,z2,z10,z129,z4,z5,z8]),(0,[z192,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z70,z103]),(0,[z1,z2,z3,z193,z4,z5,z8]),(0,[z1,z121,z3,z4,z5,z22,z8]),(0,[z194,z1,z2,z3,z5,z8,z103]),(1,[z1,z3,z4,z5,z8,z195])]],
   [[(1,[z1,z2,z196,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z197]),(0,[z54,z1,z46,z3,z4,z5,z8]),(0,[z163,z1,z2,z3,z4,z5,z25]),(0,[z1,z2,z3,z198,z4,z5,z8])],[(0,[z1,z2,z10,z26,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z199,z8]),(0,[z1,z2,z3,z43,z4,z5,z25]),(1,[z76,z1,z3,z4,z123,z8]),(0,[z200,z1,z2,z3,z4,z5,z8])],[(0,[z1,z18,z201,z3,z4,z5,z8]),(0,[z1,z24,z24,z3,z4,z5,z8]),(0,[z90,z1,z2,z3,z4,z7,z8]),(0,[z1,z202,z2,z3,z4,z5,z8]),(1,[z1,z203,z3,z4,z204,z8])],[(1,[z1,z205,z3,z4,z5,z8]),(0,[z1,z2,z3,z206,z4,z5,z8]),(0,[z1,z2,z3,z4,z207,z5,z8]),(0,[z208,z1,z2,z3,z4,z5,z8])],[(0,[z209,z1,z24,z3,z4,z5,z8]),(0,[z210,z1,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z211]),(0,[z1,z2,z3,z4,z5,z8,z212]),(0,[z1,z2,z3,z59,z4,z5,z12]),(0,[z1,z2,z3,z213,z4,z5,z8]),(0,[z1,z2,z3,z59,z4,z5,z214])],[(0,[z1,z2,z26,z4,z5,z142,z8]),(0,[z1,z2,z3,z4,z215,z5,z8]),(0,[z1,z46,z2,z3,z102,z5,z8]),(1,[z1,z2,z3,z4,z5,z12]),(0,[z1,z2,z3,z4,z5,z8,z216]),(0,[z1,z2,z3,z4,z5,z182,z25]),(1,[z1,z2,z3,z4,z5,z214])],[(0,[z1,z2,z3,z4,z5,z8,z217]),(0,[z1,z2,z218,z18,z3,z4,z5]),(1,[z1,z219,z3,z4,z5,z8]),(0,[z220,z1,z2,z3,z4,z5,z8]),(0,[z37,z1,z2,z3,z4,z5,z221]),(0,[z1,z2,z3,z222,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z52,z8]),(0,[z90,z1,z121,z2,z3,z4,z5]),(0,[z223,z1,z2,z3,z4,z5,z8])]],
   [[(0,[z0,z1,z2,z26,z4,z5,z8]),(0,[z224,z1,z2,z3,z4,z5,z8]),(0,[z1,z46,z2,z3,z62,z5,z8]),(0,[z1,z2,z3,z4,z145,z5,z12])],[(0,[z1,z2,z3,z4,z5,z225,z8]),(0,[z1,z2,z3,z226,z4,z5,z8]),(0,[z1,z2,z3,z227,z4,z5,z8]),(0,[z90,z1,z2,z3,z4,z5,z70]),(0,[z228,z1,z2,z3,z4,z5,z8]),(0,[z229,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z230]),(0,[z231,z1,z2,z3,z4,z5,z8]),(1,[z1,z3,z232,z4,z5,z8]),(0,[z1,z2,z3,z233,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z12,z212]),(0,[z1,z2,z3,z4,z234,z5,z8])],[(0,[z1,z2,z3,z4,z235,z5,z8]),(0,[z53,z1,z2,z236,z4,z5,z8]),(0,[z1,z237,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z81,z45,z8]),(0,[z69,z1,z238,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z123,z8])],[(1,[z1,z18,z3,z4,z5,z8]),(0,[z1,z2,z11,z3,z239,z5,z8]),(0,[z1,z2,z3,z240,z4,z5,z8]),(0,[z1,z2,z3,z204,z5,z120,z8]),(0,[z1,z2,z3,z241,z4,z5,z8])],[(0,[z242,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z243,z5,z8]),(0,[z76,z1,z2,z3,z4,z5,z8]),(0,[z244,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z245,z4,z5,z8]),(0,[z1,z2,z3,z43,z4,z5,z12]),(0,[z1,z2,z38,z3,z4,z142,z8]),(0,[z1,z2,z3,z213,z4,z5,z25]),(0,[z1,z2,z3,z4,z5,z8,z246])],[(1,[z24,z18,z3,z4,z5,z8]),(0,[z1,z2,z3,z247,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z248,z8]),(1,[z109,z1,z2,z4,z142,z8]),(0,[z249,z1,z2,z3,z4,z5,z8])],[(0,[z250,z1,z2,z3,z4,z5,z8]),(0,[z53,z1,z46,z2,z3,z5,z8]),(0,[z1,z2,z3,z4,z251,z5,z8]),(0,[z2,z3,z4,z5,z252,z8,z70]),(0,[z1,z2,z3,z253,z5,z22,z8]),(1,[z191,z1,z2,z160,z5,z8]),(0,[z1,z2,z3,z15,z4,z5,z8])]],
   [[(0,[z1,z18,z3,z4,z5,z8,z103]),(1,[z1,z254,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z22,z8]),(0,[z1,z121,z2,z3,z4,z5,z103]),(0,[z1,z255,z56,z3,z4,z5,z8]),(0,[z256,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z140,z16,z5]),(0,[z257,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z106,z5,z8,z103]),(1,[z1,z2,z3,z4,z5,z29]),(0,[z1,z2,z3,z4,z5,z182,z12])],[(0,[z69,z1,z24,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z258,z5,z8]),(0,[z1,z2,z3,z4,z5,z32,z103]),(0,[z1,z2,z3,z102,z4,z5,z182])],[(0,[z259,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z260,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z123,z25]),(0,[z1,z2,z3,z4,z5,z261,z8]),(1,[z1,z2,z3,z4,z16,z32])],[(1,[z1,z18,z3,z4,z5,z25]),(0,[z1,z24,z3,z102,z4,z5,z8]),(0,[z130,z1,z2,z11,z4,z5,z8]),(0,[z1,z2,z262,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z263]),(0,[z1,z2,z3,z264,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z265])],[(0,[z1,z24,z3,z4,z63,z5,z8]),(0,[z266,z1,z2,z3,z4,z5,z8]),(0,[z54,z1,z2,z3,z5,z28,z8]),(0,[z76,z1,z2,z3,z4,z5,z25])],[(0,[z1,z2,z3,z4,z5,z267,z8]),(0,[z90,z2,z3,z4,z5,z8,z70]),(0,[z268,z1,z2,z3,z4,z5,z8]),(0,[z269,z1,z2,z3,z4,z5,z8]),(0,[z76,z1,z2,z3,z4,z123,z8]),(0,[z1,z3,z4,z5,z8,z195,z103])],[(0,[z122,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z270,z3,z4,z5,z8]),(0,[z1,z110,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z271,z8])]],
   [[(0,[z1,z24,z3,z4,z5,z28,z8]),(0,[z1,z2,z3,z4,z5,z272,z8]),(1,[z1,z273,z3,z4,z5,z8]),(0,[z1,z274,z2,z3,z4,z5,z8]),(0,[z275,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z276,z4,z5,z8])],[(0,[z277,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z179,z5,z12]),(0,[z1,z2,z3,z253,z4,z5,z8]),(0,[z109,z1,z2,z4,z5,z142,z8]),(0,[z278,z1,z2,z3,z4,z5,z8])],[(1,[z187,z2,z3,z36,z5,z8]),(0,[z90,z1,z2,z3,z4,z5,z8]),(0,[z279,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z280,z5,z8]),(0,[z1,z2,z3,z281,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z282])],[(0,[z1,z2,z3,z4,z5,z283,z8]),(0,[z284,z1,z2,z3,z4,z5,z8]),(0,[z1,z121,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z137]),(0,[z1,z2,z3,z62,z57,z5,z8]),(0,[z285,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z286,z8]),(1,[z194,z1,z2,z3,z5,z103])],[(0,[z119,z1,z18,z3,z4,z5,z8]),(0,[z1,z2,z3,z287,z4,z5,z8])],[(0,[z1,z2,z3,z102,z36,z5,z8]),(0,[z1,z2,z3,z31,z4,z45,z8]),(0,[z61,z1,z2,z3,z4,z5,z8])],[(0,[z119,z2,z3,z4,z5,z45,z8]),(0,[z1,z2,z288,z3,z4,z5,z8]),(0,[z1,z2,z3,z176,z4,z5,z12]),(0,[z1,z2,z56,z3,z4,z5,z211]),(0,[z1,z2,z3,z4,z5,z182,z32])],[(0,[z1,z2,z3,z4,z5,z70,z12]),(0,[z289,z1,z290,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z291,z8]),(0,[z292,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z123,z12]),(0,[z1,z2,z3,z4,z204,z5,z293]),(0,[z1,z2,z3,z294,z4,z5,z8]),(0,[z295,z1,z2,z3,z4,z5,z8])]],
   [[(1,[z1,z18,z3,z4,z5,z12]),(0,[z76,z54,z1,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z296,z204,z5]),(0,[z122,z1,z2,z3,z4,z5,z25]),(0,[z83,z1,z3,z4,z5,z8,z103])],[(0,[z1,z2,z3,z102,z106,z5,z8]),(0,[z187,z1,z297,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z298,z8]),(0,[z76,z1,z2,z3,z4,z5,z12]),(0,[z1,z2,z3,z299,z4,z5,z8]),(0,[z61,z1,z3,z4,z5,z28,z8])],[(0,[z1,z2,z300,z3,z4,z5,z8]),(0,[z1,z2,z301,z3,z4,z5,z8]),(0,[z1,z302,z2,z3,z4,z5,z8])],[(0,[z1,z18,z3,z4,z16,z5,z8]),(0,[z90,z1,z2,z3,z4,z5,z25]),(0,[z1,z2,z3,z303,z4,z5,z8]),(0,[z72,z1,z2,z3,z4,z5,z22]),(0,[z1,z2,z10,z4,z81,z5,z8]),(1,[z1,z2,z3,z4,z5,z60]),(1,[z1,z2,z3,z5,z304,z8])],[(0,[z1,z2,z3,z4,z5,z305,z8]),(0,[z1,z2,z38,z26,z4,z5,z8]),(0,[z53,z1,z2,z3,z4,z34,z8]),(0,[z1,z2,z3,z4,z27,z5,z8]),(1,[z1,z2,z245,z4,z5,z8]),(0,[z1,z203,z2,z3,z4,z204,z8]),(0,[z1,z121,z2,z3,z4,z5,z25])],[(0,[z1,z2,z3,z4,z5,z8,z306]),(0,[z307,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z22,z12])],[(0,[z1,z2,z3,z4,z5,z308,z8]),(0,[z187,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z309]),(0,[z1,z2,z3,z4,z16,z5,z8])],[(0,[z1,z18,z129,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z310,z8]),(0,[z1,z2,z3,z4,z5,z182,z252]),(0,[z1,z46,z2,z3,z4,z5,z12]),(0,[z1,z2,z3,z4,z5,z311,z8])]],
   [[(0,[z1,z2,z3,z312,z4,z5,z8]),(0,[z313,z1,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z314]),(1,[z1,z255,z3,z4,z5,z8])],[(0,[z1,z24,z3,z4,z5,z123,z8]),(0,[z1,z2,z3,z4,z5,z8,z315]),(0,[z1,z2,z56,z3,z4,z5,z316])],[(0,[z1,z2,z129,z3,z4,z5,z8]),(0,[z1,z2,z3,z159,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z317,z8]),(0,[z318,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z319]),(0,[z1,z2,z3,z4,z5,z25,z103])],[(0,[z320,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z321,z4,z5,z8]),(0,[z322,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z323,z8])],[(0,[z1,z2,z3,z324,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z70,z32]),(0,[z1,z46,z2,z3,z43,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z325]),(0,[z122,z1,z2,z3,z4,z5,z12]),(0,[z1,z2,z3,z326,z4,z5,z8])],[(0,[z1,z46,z18,z3,z4,z5,z8]),(1,[z1,z2,z3,z188,z5,z8]),(0,[z1,z2,z3,z4,z27,z5,z25]),(0,[z130,z1,z3,z176,z4,z5,z8]),(0,[z1,z3,z43,z4,z179,z5,z8]),(0,[z1,z2,z3,z4,z5,z327,z8])],[(0,[z1,z2,z3,z4,z5,z8,z328]),(1,[z1,z297,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z329]),(0,[z330,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z331,z5,z8])],[(0,[z1,z18,z3,z59,z4,z5,z8]),(0,[z119,z1,z2,z129,z4,z5,z8]),(0,[z187,z1,z170,z3,z4,z5,z8]),(0,[z187,z1,z2,z3,z4,z5,z25]),(0,[z90,z1,z2,z3,z4,z5,z12]),(0,[z54,z1,z2,z3,z5,z8,z103]),(0,[z1,z2,z3,z4,z16,z5,z25])]],
   [[(0,[z1,z18,z3,z4,z5,z8,z12]),(0,[z1,z2,z332,z3,z4,z5,z8]),(0,[z333,z1,z2,z3,z4,z5,z8]),(0,[z1,z121,z2,z3,z4,z5,z12])],[(0,[z1,z2,z3,z4,z5,z334,z8]),(1,[z54,z1,z3,z179,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z335]),(0,[z336,z1,z2,z3,z4,z5,z8]),(0,[z337,z1,z2,z3,z4,z5,z8])],[(0,[z1,z24,z3,z4,z5,z8,z103]),(0,[z289,z1,z121,z2,z3,z4,z5]),(0,[z1,z2,z56,z3,z160,z5,z8]),(0,[z1,z255,z2,z3,z4,z5,z8])],[(0,[z338,z1,z24,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z339,z8]),(0,[z1,z2,z129,z3,z4,z5,z25]),(0,[z1,z2,z3,z4,z340,z5,z8]),(0,[z1,z341,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z342,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z343,z8]),(0,[z1,z344,z24,z3,z4,z5,z8]),(0,[z345,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z346]),(0,[z289,z1,z2,z3,z4,z5,z70]),(0,[z1,z2,z3,z347,z4,z5,z8]),(1,[z1,z2,z3,z239,z5,z8]),(0,[z1,z2,z3,z4,z5,z348,z8])],[(0,[z90,z1,z18,z3,z4,z5,z8]),(0,[z37,z1,z24,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z221]),(0,[z1,z2,z3,z349,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z25,z8])],[(0,[z0,z1,z18,z3,z4,z5,z8]),(0,[z1,z121,z18,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z9,z8]),(0,[z1,z2,z3,z350,z4,z5,z8]),(1,[z1,z2,z294,z4,z5,z8])],[(0,[z1,z2,z3,z4,z351,z5,z8]),(0,[z187,z2,z3,z36,z4,z5,z8]),(0,[z1,z2,z3,z4,z7,z5,z8]),(0,[z1,z2,z3,z4,z5,z352,z8]),(0,[z353,z1,z2,z3,z4,z5,z8])]],
   [[(0,[z1,z18,z3,z43,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z354]),(0,[z109,z1,z2,z10,z4,z5,z8])],[(0,[z64,z65,z2,z3,z4,z5,z8]),(0,[z355,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z27,z5,z12]),(0,[z1,z2,z3,z356,z4,z5,z8]),(0,[z1,z2,z3,z62,z102,z5,z8])],[(0,[z1,z2,z3,z357,z4,z5,z8]),(0,[z1,z46,z2,z3,z160,z5,z8]),(0,[z72,z1,z3,z43,z4,z5,z8])],[(0,[z358,z1,z2,z3,z4,z5,z8]),(0,[z53,z187,z2,z3,z4,z5,z8]),(0,[z187,z1,z2,z3,z4,z5,z12]),(0,[z1,z2,z3,z4,z5,z359,z8]),(0,[z1,z2,z3,z57,z4,z5,z8]),(0,[z1,z2,z3,z4,z16,z5,z12]),(0,[z1,z2,z3,z4,z5,z8,z195]),(0,[z1,z2,z3,z4,z140,z5,z103])],[(0,[z1,z18,z3,z4,z5,z182,z8]),(0,[z1,z2,z3,z360,z4,z5,z8]),(0,[z1,z2,z11,z3,z4,z5,z361]),(1,[z1,z2,z3,z4,z5,z25]),(0,[z1,z2,z3,z4,z5,z8,z362]),(0,[z194,z1,z2,z3,z102,z5,z8]),(0,[z363,z1,z2,z3,z4,z5,z8])],[(0,[z1,z18,z3,z4,z5,z8,z32]),(0,[z76,z1,z24,z3,z4,z5,z8]),(0,[z2,z3,z26,z4,z5,z45,z8]),(0,[z1,z2,z129,z38,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z216,z12]),(0,[z1,z364,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z365,z5,z8])],[(0,[z1,z2,z3,z4,z5,z366,z8]),(0,[z130,z1,z42,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z367,z5,z8]),(0,[z1,z2,z3,z4,z5,z25,z25]),(0,[z194,z1,z2,z3,z4,z5,z103])],[(0,[z1,z2,z3,z368,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z369,z8]),(0,[z1,z2,z129,z3,z4,z5,z12]),(0,[z1,z203,z3,z176,z4,z5,z8]),(0,[z1,z2,z3,z62,z4,z28,z8])]],
   [[(0,[z0,z119,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z197,z8]),(0,[z370,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z371,z8]),(0,[z1,z2,z3,z4,z5,z8,z32]),(0,[z1,z2,z372,z3,z4,z5,z8])],[(0,[z1,z2,z129,z4,z5,z8,z12]),(0,[z1,z2,z3,z373,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z325]),(1,[z1,z2,z3,z4,z5,z374])],[(1,[z1,z2,z3,z375,z5,z8]),(0,[z1,z2,z3,z4,z376,z5,z8]),(0,[z90,z1,z273,z3,z4,z5,z8]),(1,[z1,z2,z3,z377,z5,z8]),(0,[z1,z2,z378,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z160,z5,z8]),(0,[z379,z1,z2,z3,z4,z5,z8])],[(0,[z1,z380,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z381,z5,z8]),(0,[z1,z2,z3,z382,z4,z5,z8]),(1,[z1,z2,z3,z102,z5,z182])],[(0,[z1,z332,z18,z3,z4,z5,z8]),(0,[z191,z1,z18,z3,z4,z5,z8]),(0,[z1,z18,z3,z4,z179,z5,z8]),(0,[z119,z1,z2,z3,z4,z5,z8]),(0,[z383,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z57,z4,z5,z25]),(0,[z1,z2,z3,z4,z384,z5,z8])],[(0,[z1,z24,z3,z4,z16,z5,z8]),(0,[z0,z1,z2,z3,z4,z385,z8]),(0,[z386,z1,z2,z3,z4,z5,z8]),(0,[z90,z1,z2,z3,z4,z5,z252]),(0,[z1,z2,z3,z387,z4,z5,z8]),(0,[z1,z2,z3,z232,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z12,z32]),(0,[z1,z2,z3,z4,z5,z8,z388])],[(0,[z1,z18,z3,z4,z5,z8,z217]),(0,[z389,z1,z2,z3,z4,z5,z8]),(0,[z69,z1,z2,z3,z4,z45,z8]),(0,[z1,z2,z3,z4,z5,z390,z8]),(0,[z1,z56,z3,z232,z4,z5,z8]),(0,[z1,z2,z38,z4,z81,z5,z8]),(0,[z1,z2,z3,z4,z140,z5,z8])],[(0,[z1,z2,z18,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z179,z5,z8]),(0,[z109,z1,z2,z3,z4,z81,z8]),(0,[z391,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z33,z4,z140,z5,z8])]],
   [[(0,[z392,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z393,z3,z4,z5,z8]),(0,[z1,z2,z3,z342,z4,z5,z12]),(0,[z1,z2,z3,z59,z5,z28,z8]),(0,[z1,z2,z3,z4,z5,z8,z394]),(0,[z1,z2,z3,z4,z16,z5,z32])],[(0,[z1,z18,z3,z176,z4,z5,z8]),(0,[z395,z1,z2,z3,z4,z5,z8]),(0,[z1,z24,z129,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z396,z5,z8]),(0,[z0,z1,z2,z129,z4,z5,z8]),(0,[z53,z1,z2,z3,z4,z5,z197]),(0,[z397,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z398,z4,z5,z8]),(0,[z1,z2,z4,z81,z5,z8,z12]),(0,[z1,z3,z4,z5,z126,z28,z8]),(0,[z194,z1,z2,z3,z4,z5,z8])],[(0,[z399,z1,z2,z3,z4,z5,z8]),(0,[z1,z18,z3,z4,z5,z123,z8]),(0,[z1,z2,z3,z400,z4,z5,z8]),(0,[z401,z1,z2,z3,z4,z5,z8]),(0,[z1,z402,z2,z3,z4,z5,z8]),(0,[z191,z1,z2,z56,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z25,z12])],[(0,[z64,z1,z24,z3,z4,z5,z8]),(0,[z1,z2,z57,z4,z160,z5,z8]),(0,[z1,z2,z3,z4,z160,z5,z25]),(0,[z109,z39,z2,z3,z4,z5,z8])],[(0,[z1,z2,z254,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z403,z5,z8]),(0,[z404,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z176,z4,z5,z8]),(0,[z1,z2,z405,z3,z4,z5,z8]),(0,[z1,z2,z3,z406,z4,z5,z8])],[(1,[z105,z1,z18,z3,z4,z5]),(0,[z119,z1,z2,z3,z4,z5,z25]),(0,[z407,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z408,z4,z5,z8]),(0,[z1,z2,z56,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z409,z8]),(0,[z109,z1,z48,z3,z4,z5,z8]),(1,[z1,z2,z3,z410,z5,z8]),(0,[z411,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z304,z8])],[(0,[z412,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z413]),(0,[z69,z1,z414,z3,z4,z5,z8]),(0,[z90,z1,z2,z245,z4,z5,z8]),(0,[z54,z1,z2,z3,z57,z5,z8]),(1,[z1,z46,z3,z43,z5,z8]),(0,[z1,z2,z3,z102,z5,z28,z8])],[(1,[z1,z2,z68,z3,z5,z8]),(0,[z1,z2,z3,z4,z415,z5,z8]),(0,[z1,z2,z3,z416,z4,z5,z8]),(0,[z72,z289,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z417,z5,z8]),(0,[z1,z2,z3,z4,z140,z5,z25])]],
   [[(0,[z1,z18,z3,z4,z5,z22,z8]),(0,[z1,z2,z18,z3,z4,z5,z25]),(0,[z1,z2,z3,z4,z5,z8,z418]),(0,[z1,z2,z419,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z179,z5,z25]),(0,[z1,z2,z3,z57,z4,z5,z12]),(0,[z1,z2,z3,z4,z5,z142,z8]),(0,[z1,z420,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z63,z5,z28,z8])],[(0,[z1,z24,z3,z59,z4,z5,z8]),(1,[z1,z421,z3,z4,z5,z8]),(0,[z54,z1,z3,z4,z179,z5,z8]),(0,[z191,z1,z2,z3,z160,z5,z8]),(0,[z1,z2,z3,z422,z4,z5,z8])],[(0,[z1,z24,z3,z4,z5,z8,z12]),(0,[z1,z2,z3,z4,z423,z5,z8]),(0,[z1,z2,z3,z36,z5,z8,z103]),(0,[z1,z2,z3,z4,z424,z5,z8]),(0,[z1,z2,z3,z4,z5,z425,z8]),(0,[z1,z2,z3,z4,z296,z5,z8]),(0,[z426,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z160,z5,z28,z8]),(0,[z1,z2,z3,z4,z5,z25,z168]),(0,[z1,z2,z3,z4,z5,z8,z427]),(0,[z194,z1,z2,z3,z4,z5,z25])],[(1,[z105,z1,z2,z3,z4,z5]),(0,[z1,z24,z3,z135,z4,z5,z8]),(0,[z1,z2,z4,z140,z428,z5,z8])],[(0,[z53,z1,z18,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z298,z8]),(0,[z1,z2,z3,z4,z5,z252,z103]),(0,[z1,z42,z2,z3,z4,z5,z8]),(0,[z429,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z8,z6]),(0,[z430,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z176,z4,z5,z25]),(0,[z1,z46,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z431,z4,z5,z8])],[(0,[z0,z2,z3,z26,z4,z5,z8]),(0,[z54,z1,z3,z176,z4,z5,z8]),(0,[z1,z2,z3,z4,z432,z5,z8]),(0,[z1,z2,z3,z433,z4,z5,z8]),(0,[z1,z2,z56,z3,z4,z5,z25]),(0,[z1,z2,z434,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z435,z5,z8]),(0,[z1,z2,z3,z4,z188,z5,z8]),(0,[z436,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z160,z5,z12]),(0,[z1,z2,z3,z4,z437,z5,z8]),(0,[z1,z2,z3,z438,z4,z5,z8]),(0,[z1,z2,z10,z3,z4,z5,z8]),(0,[z1,z2,z4,z5,z25,z8,z12]),(0,[z1,z2,z3,z4,z5,z25,z32])]],
   [[(0,[z439,z1,z2,z3,z4,z5,z8]),(0,[z1,z3,z43,z4,z204,z5,z8]),(0,[z1,z2,z3,z4,z5,z440,z8]),(1,[z1,z2,z33,z4,z5,z8])],[(1,[z1,z2,z3,z4,z308,z8]),(0,[z119,z1,z2,z3,z4,z5,z12]),(0,[z53,z1,z254,z3,z4,z5,z8]),(1,[z90,z2,z3,z4,z5,z70]),(0,[z1,z2,z3,z4,z5,z8,z441]),(0,[z442,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z142,z25])],[(0,[z1,z24,z3,z57,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z443]),(0,[z1,z24,z3,z43,z4,z5,z8]),(0,[z119,z1,z219,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z444,z5,z8]),(0,[z1,z2,z3,z445,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z214,z8])],[(0,[z1,z18,z3,z4,z5,z8,z137]),(1,[z1,z88,z3,z4,z5,z8]),(0,[z37,z1,z2,z446,z4,z5,z8]),(0,[z1,z2,z3,z4,z63,z45,z8]),(0,[z1,z121,z2,z3,z4,z5,z137]),(0,[z1,z2,z3,z4,z447,z5,z8]),(0,[z1,z2,z3,z4,z140,z5,z12]),(0,[z1,z2,z3,z4,z5,z425,z25]),(0,[z1,z2,z3,z62,z59,z5,z8])],[(0,[z1,z2,z18,z3,z4,z5,z12]),(1,[z1,z238,z3,z4,z5,z8]),(0,[z289,z2,z3,z4,z5,z252,z8]),(0,[z76,z1,z203,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z4,z5,z8]),(1,[z1,z414,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z448,z5,z8]),(0,[z1,z42,z2,z3,z4,z5,z25]),(0,[z54,z1,z3,z4,z5,z22,z8]),(0,[z72,z1,z3,z4,z5,z8,z137]),(0,[z449,z1,z2,z3,z4,z5,z8])],[(0,[z1,z24,z3,z4,z5,z182,z8]),(0,[z0,z1,z2,z3,z4,z5,z8]),(0,[z450,z1,z2,z3,z4,z5,z8]),(0,[z1,z46,z2,z3,z4,z5,z25]),(0,[z1,z2,z3,z4,z451,z5,z8]),(0,[z1,z452,z2,z3,z4,z5,z8]),(0,[z194,z1,z2,z3,z4,z5,z12]),(0,[z1,z2,z3,z431,z4,z5,z25])],[(0,[z1,z24,z3,z4,z5,z8,z32]),(0,[z1,z2,z3,z4,z453,z5,z8]),(0,[z54,z187,z1,z2,z3,z5,z8]),(0,[z37,z1,z2,z3,z4,z5,z454]),(0,[z1,z2,z3,z4,z5,z8,z455]),(0,[z1,z2,z3,z4,z5,z252,z8]),(1,[z1,z42,z11,z4,z5,z8]),(0,[z1,z2,z3,z456,z4,z5,z8])]],
   [[(0,[z289,z1,z18,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z25,z252]),(0,[z1,z2,z10,z3,z4,z5,z25]),(0,[z1,z2,z457,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z310,z5,z8]),(0,[z37,z1,z2,z458,z4,z5,z8]),(1,[z1,z2,z4,z5,z25,z12]),(0,[z1,z2,z3,z4,z459,z5,z8]),(0,[z1,z2,z3,z16,z5,z304,z8])],[(0,[z460,z1,z2,z3,z4,z5,z8]),(0,[z461,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z75,z3,z4,z5,z8]),(0,[z1,z203,z2,z3,z4,z5,z8]),(0,[z462,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z56,z3,z4,z5,z12]),(0,[z1,z2,z38,z3,z4,z81,z8])],[(0,[z1,z1,z18,z3,z4,z5,z8]),(0,[z0,z1,z150,z3,z4,z5,z8]),(0,[z1,z2,z3,z57,z36,z5,z8]),(0,[z54,z1,z2,z3,z179,z5,z8]),(0,[z1,z2,z463,z3,z4,z5,z8]),(0,[z464,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z465,z5,z8]),(0,[z1,z2,z3,z4,z466,z5,z8]),(0,[z1,z2,z3,z4,z140,z5,z182])],[(1,[z1,z24,z3,z4,z5,z8]),(0,[z1,z2,z3,z467,z4,z5,z8]),(0,[z468,z1,z2,z3,z4,z5,z8]),(0,[z1,z18,z3,z4,z27,z5,z8]),(0,[z194,z1,z18,z3,z4,z5,z8]),(0,[z1,z469,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z27,z8,z32]),(0,[z76,z1,z3,z4,z5,z123,z8])],[(0,[z1,z24,z3,z4,z140,z5,z8]),(0,[z0,z1,z2,z3,z159,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z470]),(0,[z37,z1,z2,z3,z471,z5,z8]),(0,[z1,z2,z3,z4,z5,z45,z8]),(0,[z1,z203,z3,z4,z204,z5,z8]),(0,[z1,z2,z3,z4,z472,z5,z8]),(1,[z1,z2,z3,z473,z5,z8]),(0,[z1,z2,z3,z4,z5,z142,z12]),(0,[z1,z2,z3,z4,z5,z474,z8])],[(0,[z1,z24,z3,z4,z179,z5,z8]),(0,[z1,z2,z3,z4,z475,z5,z8]),(0,[z476,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z477,z8]),(0,[z478,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z479,z5,z8]),(0,[z1,z2,z3,z4,z5,z480,z8]),(0,[z1,z2,z3,z4,z16,z8,z32])],[(0,[z481,z1,z18,z3,z4,z5,z8]),(0,[z0,z1,z2,z3,z4,z5,z25]),(0,[z1,z2,z3,z236,z4,z5,z8]),(0,[z1,z2,z3,z57,z106,z5,z8]),(0,[z54,z1,z42,z3,z4,z5,z8]),(0,[z482,z1,z2,z3,z4,z5,z8])]],
   [[(0,[z105,z1,z18,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z45,z8,z32])],[(0,[z483,z1,z2,z3,z4,z5,z8]),(0,[z1,z40,z2,z3,z4,z5,z8]),(0,[z37,z1,z2,z3,z4,z45,z8]),(0,[z1,z42,z2,z3,z4,z5,z12]),(0,[z1,z2,z484,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z485,z5,z8]),(0,[z109,z1,z173,z3,z4,z5,z8]),(0,[z209,z1,z2,z10,z4,z5,z8]),(0,[z486,z1,z2,z3,z4,z5,z8])],[(1,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z487,z4,z5,z8]),(0,[z1,z2,z297,z3,z4,z5,z8]),(0,[z1,z2,z176,z4,z5,z8,z12]),(0,[z1,z2,z3,z4,z5,z12,z470])],[(0,[z130,z1,z18,z3,z4,z5,z8]),(0,[z1,z24,z3,z176,z4,z5,z8]),(0,[z1,z2,z3,z4,z488,z5,z8]),(0,[z1,z2,z3,z4,z489,z5,z8])],[(0,[z1,z24,z3,z4,z235,z5,z8]),(0,[z1,z24,z56,z3,z4,z5,z8]),(0,[z1,z490,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z377,z5,z8]),(0,[z54,z1,z2,z3,z102,z5,z8]),(1,[z1,z2,z3,z4,z5,z491]),(0,[z191,z1,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z265]),(0,[z1,z2,z10,z3,z4,z5,z12]),(0,[z1,z2,z3,z5,z28,z8,z103])],[(1,[z1,z24,z3,z4,z5,z25]),(0,[z1,z2,z3,z4,z63,z27,z8]),(0,[z1,z2,z3,z492,z4,z5,z8]),(0,[z493,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z211,z8]),(0,[z1,z2,z3,z494,z4,z5,z8]),(0,[z1,z2,z3,z4,z495,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z496])],[(0,[z1,z2,z3,z4,z5,z45,z25]),(1,[z1,z2,z3,z253,z5,z8]),(0,[z1,z2,z3,z62,z160,z5,z8]),(0,[z1,z2,z3,z4,z5,z374,z8])],[(0,[z1,z2,z2,z3,z4,z5,z8]),(0,[z1,z42,z18,z3,z4,z5,z8]),(0,[z497,z1,z2,z3,z4,z5,z8]),(0,[z54,z1,z2,z3,z62,z5,z8]),(0,[z1,z2,z3,z445,z4,z5,z12]),(0,[z1,z2,z498,z3,z4,z5,z8])]],
   [[(0,[z1,z18,z3,z499,z4,z5,z8]),(0,[z53,z1,z2,z3,z4,z310,z8]),(0,[z37,z1,z288,z3,z4,z5,z8]),(0,[z500,z1,z2,z3,z4,z5,z8]),(1,[z1,z3,z4,z5,z126,z8]),(0,[z1,z2,z3,z4,z501,z5,z8]),(0,[z502,z1,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z15,z5,z8])],[(0,[z0,z1,z205,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z52]),(0,[z503,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z140,z5,z252]),(0,[z1,z2,z3,z4,z504,z5,z8])],[(0,[z1,z24,z3,z4,z5,z22,z8]),(0,[z1,z2,z3,z31,z4,z27,z8]),(0,[z1,z2,z3,z4,z204,z5,z8]),(0,[z505,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z499,z4,z5,z8]),(0,[z0,z1,z2,z3,z4,z5,z12]),(0,[z1,z2,z3,z4,z5,z506,z8]),(0,[z1,z2,z3,z507,z4,z5,z8]),(0,[z1,z161,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z446,z4,z5,z8]),(0,[z1,z48,z2,z3,z4,z5,z8]),(0,[z508,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z150,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z252,z12]),(0,[z1,z2,z3,z4,z509,z5,z8]),(0,[z1,z510,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z43,z4,z5,z491]),(0,[z109,z1,z2,z3,z4,z5,z12]),(0,[z1,z2,z3,z4,z489,z5,z25])],[(0,[z1,z18,z3,z4,z5,z25,z8]),(0,[z1,z24,z3,z260,z4,z5,z8]),(0,[z511,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z512,z5,z8]),(0,[z1,z2,z3,z4,z5,z25,z137]),(0,[z191,z1,z2,z3,z4,z5,z25]),(0,[z1,z2,z38,z3,z4,z5,z111])],[(0,[z1,z2,z3,z4,z5,z8,z513]),(0,[z1,z2,z3,z4,z514,z5,z8]),(0,[z515,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z516,z5,z8]),(0,[z1,z2,z3,z4,z517,z5,z8]),(0,[z1,z2,z3,z31,z4,z16,z8])],[(0,[z1,z88,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z471,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z518,z8]),(0,[z519,z1,z2,z3,z4,z5,z8]),(0,[z1,z203,z2,z3,z4,z5,z12]),(1,[z1,z2,z3,z5,z8,z23]),(0,[z1,z2,z520,z3,z4,z5,z8])]],
   [[(1,[z130,z1,z176,z4,z5,z8]),(1,[z1,z2,z176,z4,z5,z12]),(0,[z521,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z465,z5,z12]),(0,[z1,z2,z3,z5,z182,z8,z103])],[(0,[z1,z2,z3,z4,z522,z5,z8]),(0,[z392,z1,z24,z3,z4,z5,z8]),(0,[z1,z24,z3,z4,z5,z8,z443]),(1,[z1,z24,z3,z4,z5,z12]),(0,[z1,z2,z3,z4,z5,z8,z454]),(0,[z54,z1,z2,z3,z4,z5,z8]),(0,[z72,z1,z2,z177,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z523]),(0,[z1,z2,z173,z3,z4,z5,z8])],[(0,[z109,z1,z18,z3,z4,z5,z8]),(0,[z1,z24,z3,z4,z5,z272,z8]),(0,[z1,z2,z196,z3,z4,z5,z8]),(0,[z53,z2,z3,z4,z106,z5,z8]),(0,[z1,z2,z3,z4,z5,z45,z12]),(0,[z69,z2,z3,z4,z27,z5,z8]),(0,[z1,z524,z2,z3,z4,z5,z8]),(0,[z1,z2,z38,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z525,z5,z8])],[(0,[z1,z18,z3,z57,z4,z5,z8]),(0,[z289,z1,z75,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z131]),(0,[z130,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z204,z5,z25]),(0,[z1,z121,z2,z3,z4,z5,z182])],[(1,[z1,z2,z218,z3,z4,z5]),(0,[z53,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z526,z8]),(0,[z54,z1,z3,z4,z204,z5,z8]),(1,[z110,z2,z3,z4,z5,z8])],[(0,[z1,z203,z18,z3,z4,z5,z8]),(0,[z1,z24,z3,z4,z5,z8,z137]),(0,[z1,z2,z3,z4,z5,z8,z527]),(0,[z1,z121,z2,z3,z4,z140,z5]),(0,[z1,z2,z3,z4,z5,z528,z8])],[(0,[z1,z18,z3,z4,z5,z366,z8]),(0,[z1,z24,z3,z4,z5,z252,z8]),(0,[z90,z1,z2,z3,z4,z298,z8]),(0,[z1,z2,z3,z4,z529,z5,z8]),(0,[z530,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z531,z8]),(1,[z72,z1,z3,z4,z5,z137]),(0,[z1,z2,z3,z4,z532,z5,z8])],[(0,[z533,z1,z2,z3,z4,z5,z8]),(0,[z534,z1,z2,z3,z4,z5,z8]),(0,[z1,z3,z176,z43,z4,z5,z8]),(0,[z1,z2,z3,z535,z4,z5,z8])]],
   [[(0,[z536,z1,z2,z3,z4,z5,z8]),(0,[z1,z121,z2,z3,z4,z5,z32])],[(0,[z1,z2,z3,z36,z160,z5,z8]),(0,[z1,z2,z3,z4,z5,z252,z32]),(0,[z1,z2,z3,z4,z5,z537,z8]),(0,[z538,z1,z2,z3,z4,z5,z8]),(0,[z191,z1,z2,z3,z4,z5,z12]),(0,[z1,z2,z38,z3,z4,z5,z74])],[(0,[z1,z18,z3,z4,z160,z5,z8]),(0,[z1,z2,z3,z539,z4,z5,z8]),(0,[z1,z2,z3,z4,z540,z5,z8])],[(0,[z1,z2,z3,z26,z4,z5,z8]),(0,[z1,z2,z3,z106,z160,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z541]),(0,[z542,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z38,z3,z4,z5,z25]),(0,[z1,z543,z2,z3,z4,z5,z8]),(1,[z209,z1,z2,z4,z5,z12])],[(0,[z483,z1,z18,z3,z4,z5,z8]),(0,[z0,z1,z2,z3,z4,z308,z8]),(0,[z1,z421,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z491,z8]),(0,[z1,z2,z544,z3,z4,z5,z8]),(0,[z497,z1,z2,z3,z4,z5,z12])],[(0,[z1,z2,z219,z3,z4,z5,z8]),(0,[z53,z1,z2,z3,z4,z5,z25]),(0,[z1,z2,z3,z4,z5,z8,z545])],[(0,[z1,z18,z3,z4,z140,z5,z8]),(0,[z1,z24,z3,z4,z27,z5,z8]),(0,[z1,z46,z24,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z328]),(0,[z1,z3,z4,z204,z5,z123,z8]),(0,[z1,z2,z3,z4,z140,z8,z32])],[(0,[z1,z18,z18,z3,z4,z5,z8]),(0,[z546,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z70]),(1,[z1,z290,z3,z4,z5,z8]),(0,[z1,z2,z10,z176,z4,z5,z8]),(0,[z1,z2,z3,z4,z204,z5,z12]),(0,[z1,z2,z3,z547,z4,z5,z8]),(0,[z1,z548,z2,z3,z4,z5,z8])]],
   [[(0,[z2,z129,z3,z26,z4,z5,z8]),(0,[z289,z1,z2,z3,z4,z5,z8]),(0,[z1,z162,z2,z3,z4,z5,z8]),(1,[z1,z2,z393,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z293]),(0,[z508,z1,z2,z3,z4,z5,z12])],[(0,[z72,z1,z18,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z106,z5,z8]),(0,[z1,z2,z549,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z550,z8]),(0,[z1,z2,z3,z62,z4,z5,z8])],[(1,[z1,z2,z446,z4,z5,z8])],[(0,[z1,z1,z2,z3,z4,z5,z8]),(0,[z122,z1,z24,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z551,z5,z8]),(0,[z1,z2,z3,z4,z552,z5,z8]),(0,[z515,z1,z2,z3,z4,z5,z12])],[(0,[z1,z93,z18,z3,z4,z5,z8]),(0,[z553,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z26,z4,z5,z25]),(0,[z1,z2,z3,z554,z4,z5,z8]),(0,[z53,z1,z2,z196,z4,z5,z8]),(0,[z2,z3,z36,z4,z106,z5,z8]),(0,[z542,z1,z2,z3,z4,z5,z25])],[(0,[z1,z18,z56,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z555,z8])],[(0,[z90,z1,z24,z3,z4,z5,z8]),(0,[z54,z1,z2,z3,z4,z5,z12]),(0,[z1,z2,z3,z4,z5,z556,z8]),(0,[z1,z557,z2,z3,z4,z5,z8])],[(0,[z481,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z558,z5,z8]),(0,[z1,z121,z24,z3,z4,z5,z8]),(0,[z559,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z560,z3,z4,z5,z8]),(0,[z561,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z141,z4,z5,z8]),(0,[z1,z2,z3,z4,z473,z5,z8]),(0,[z1,z2,z3,z410,z4,z5,z8]),(0,[z1,z2,z38,z3,z4,z5,z12]),(0,[z1,z2,z3,z4,z562,z5,z8])]],
   [[(0,[z1,z18,z3,z4,z5,z142,z8]),(0,[z105,z1,z2,z3,z4,z5,z8]),(1,[z1,z2,z458,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z131]),(0,[z1,z563,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z564,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z565,z8]),(1,[z109,z1,z2,z4,z5,z12]),(0,[z209,z1,z2,z3,z4,z5,z8])],[(0,[z1,z24,z3,z4,z204,z5,z8]),(0,[z53,z1,z2,z3,z4,z5,z12]),(0,[z187,z1,z2,z3,z36,z5,z8]),(0,[z2,z3,z4,z27,z5,z45,z8]),(0,[z289,z1,z2,z3,z4,z5,z25]),(0,[z1,z3,z176,z4,z5,z123,z8]),(0,[z1,z566,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z567,z5,z8]),(0,[z1,z2,z3,z4,z568,z5,z8])],[(0,[z1,z2,z3,z4,z106,z5,z25]),(0,[z569,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z62,z4,z5,z25])],[(0,[z1,z2,z129,z4,z160,z5,z8]),(0,[z130,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z361]),(0,[z54,z1,z2,z3,z43,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z570]),(0,[z1,z2,z3,z4,z5,z571,z8])],[(0,[z54,z1,z18,z3,z4,z5,z8]),(0,[z572,z1,z2,z3,z4,z5,z8]),(0,[z37,z69,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z471,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z573]),(0,[z574,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z57,z5,z28,z8]),(0,[z1,z2,z3,z102,z5,z182,z8]),(0,[z1,z2,z3,z575,z4,z5,z8])],[(0,[z1,z2,z3,z576,z4,z5,z8]),(0,[z1,z469,z24,z3,z4,z5,z8]),(0,[z187,z1,z2,z3,z106,z5,z8]),(0,[z1,z2,z3,z577,z4,z5,z8]),(0,[z76,z1,z3,z43,z4,z5,z8]),(0,[z1,z2,z3,z578,z4,z5,z8]),(0,[z1,z2,z3,z59,z4,z63,z8])],[(0,[z579,z1,z2,z3,z4,z5,z8]),(0,[z69,z2,z3,z26,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z580,z8]),(0,[z1,z2,z581,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z555,z25]),(0,[z1,z2,z3,z4,z5,z25,z362]),(0,[z582,z1,z2,z3,z4,z5,z8])],[(0,[z1,z18,z10,z3,z4,z5,z8]),(0,[z1,z24,z3,z4,z5,z25,z8]),(0,[z1,z2,z3,z4,z5,z583,z8]),(0,[z1,z2,z273,z3,z4,z5,z8]),(0,[z1,z2,z584,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z585,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z586]),(0,[z1,z2,z3,z4,z5,z556,z25]),(0,[z1,z2,z3,z4,z5,z8,z587])]],
   [[(0,[z1,z2,z3,z26,z4,z5,z12]),(0,[z1,z2,z238,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z588,z8]),(0,[z1,z2,z3,z589,z4,z5,z8])],[(0,[z1,z18,z3,z4,z5,z590,z8]),(0,[z591,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z239,z4,z5,z8]),(0,[z1,z2,z3,z4,z592,z5,z8]),(0,[z209,z1,z2,z3,z4,z5,z25])],[(0,[z187,z1,z24,z3,z4,z5,z8])],[(0,[z37,z2,z3,z4,z5,z45,z8]),(0,[z69,z1,z2,z3,z4,z27,z8]),(0,[z1,z2,z3,z4,z5,z593,z8])],[(1,[z17,z1,z2,z3,z5,z8]),(0,[z1,z2,z3,z4,z5,z590,z8]),(0,[z1,z2,z3,z36,z4,z5,z8]),(0,[z130,z1,z2,z3,z4,z5,z25]),(0,[z1,z594,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z595,z5,z8]),(0,[z1,z2,z3,z4,z5,z596,z8]),(0,[z597,z1,z2,z3,z4,z5,z8])],[(0,[z24,z2,z18,z3,z4,z5,z8]),(0,[z1,z490,z24,z3,z4,z5,z8]),(0,[z191,z1,z24,z3,z4,z5,z8]),(0,[z289,z1,z2,z3,z4,z5,z12]),(1,[z1,z2,z3,z4,z5,z293])],[(0,[z1,z2,z3,z4,z106,z5,z12]),(0,[z1,z2,z3,z62,z4,z5,z12])],[(0,[z1,z18,z3,z4,z5,z252,z8]),(1,[z1,z288,z3,z4,z5,z8])]],
   [[(0,[z119,z2,z129,z3,z4,z5,z8]),(0,[z1,z2,z598,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z599,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z600])],[(0,[z1,z2,z129,z4,z5,z142,z8]),(0,[z1,z601,z2,z3,z4,z5,z8]),(0,[z54,z1,z2,z3,z160,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z23]),(0,[z1,z2,z3,z4,z5,z8,z178])],[(0,[z1,z24,z3,z26,z4,z5,z8]),(1,[z1,z2,z3,z602,z5,z8]),(0,[z109,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z111,z8]),(1,[z1,z2,z3,z31,z4,z140])],[(0,[z65,z1,z18,z3,z4,z5,z8]),(0,[z603,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z314,z8]),(1,[z1,z2,z56,z57,z5,z8])],[(0,[z604,z1,z2,z3,z4,z5,z8]),(0,[z1,z24,z3,z4,z160,z5,z8]),(0,[z605,z1,z2,z3,z4,z5,z8]),(0,[z53,z1,z2,z3,z36,z5,z8]),(0,[z606,z1,z2,z3,z4,z5,z8]),(0,[z1,z42,z203,z3,z4,z5,z8]),(0,[z1,z2,z3,z141,z204,z5,z8]),(0,[z191,z1,z2,z3,z4,z5,z314])],[(0,[z1,z18,z3,z4,z5,z45,z8]),(0,[z1,z2,z26,z4,z5,z8,z12]),(0,[z119,z1,z421,z3,z4,z5,z8]),(0,[z1,z2,z3,z36,z4,z5,z25]),(0,[z191,z1,z2,z3,z4,z5,z265]),(0,[z607,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z81,z5,z8]),(0,[z209,z1,z2,z3,z4,z5,z12]),(0,[z1,z563,z2,z3,z4,z5,z12]),(0,[z1,z2,z3,z4,z608,z5,z8])],[(0,[z1,z2,z3,z4,z609,z5,z8]),(0,[z610,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z611]),(0,[z72,z1,z2,z3,z4,z5,z103]),(0,[z612,z1,z2,z3,z4,z5,z8])],[(0,[z613,z1,z2,z3,z4,z5,z8]),(0,[z209,z1,z2,z4,z5,z8,z12])]],
   [[(0,[z1,z24,z3,z62,z4,z5,z8]),(0,[z614,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z34,z8]),(0,[z1,z2,z3,z4,z5,z182,z70]),(0,[z130,z1,z2,z3,z4,z5,z12]),(0,[z1,z2,z3,z4,z5,z615,z8]),(1,[z1,z2,z3,z4,z5,z361]),(0,[z1,z2,z3,z4,z5,z8,z616])],[(0,[z1,z24,z18,z3,z4,z5,z8]),(0,[z1,z2,z4,z81,z5,z142,z8]),(0,[z1,z2,z3,z4,z5,z617,z12]),(0,[z194,z1,z2,z3,z4,z5,z182])],[(0,[z618,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z619,z4,z5,z8])],[(0,[z209,z1,z18,z3,z4,z5,z8]),(0,[z17,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z218,z3,z4,z5,z8]),(0,[z1,z24,z3,z4,z396,z5,z8]),(0,[z620,z1,z2,z3,z4,z5,z8]),(0,[z109,z1,z2,z3,z4,z5,z25]),(0,[z1,z621,z2,z3,z4,z5,z8])],[(0,[z1,z2,z622,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z623,z5,z8]),(0,[z1,z42,z11,z3,z4,z5,z8]),(0,[z624,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z625]),(0,[z1,z2,z3,z4,z5,z25,z427])],[(0,[z1,z2,z3,z4,z626,z5,z8])],[(0,[z1,z2,z3,z627,z4,z5,z8]),(0,[z628,z1,z2,z3,z4,z5,z8]),(0,[z1,z46,z2,z3,z5,z28,z8]),(0,[z1,z203,z2,z3,z4,z5,z25]),(0,[z1,z2,z3,z4,z81,z5,z25])],[(0,[z1,z2,z3,z4,z375,z5,z8]),(1,[z1,z2,z26,z4,z5,z12]),(0,[z1,z203,z2,z3,z4,z123,z8]),(1,[z1,z2,z3,z4,z296,z5]),(0,[z1,z2,z56,z57,z4,z5,z8]),(0,[z1,z2,z3,z4,z629,z5,z8]),(0,[z1,z2,z630,z3,z4,z5,z8])]],
   [[(0,[z1,z2,z3,z4,z127,z5,z8]),(0,[z0,z1,z2,z3,z375,z5,z8]),(0,[z1,z2,z3,z4,z5,z631,z8]),(0,[z1,z2,z3,z4,z5,z632,z8]),(0,[z1,z2,z3,z4,z5,z137,z12]),(0,[z109,z1,z2,z3,z4,z5,z325]),(0,[z109,z1,z2,z3,z4,z5,z374])],[(0,[z1,z2,z3,z36,z4,z5,z12]),(0,[z1,z2,z3,z62,z36,z5,z8]),(0,[z1,z2,z3,z4,z633,z5,z8]),(0,[z72,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z634,z5,z8]),(0,[z1,z2,z3,z4,z5,z12,z625])],[(0,[z1,z18,z3,z4,z204,z5,z8]),(0,[z1,z24,z3,z4,z5,z142,z8]),(0,[z1,z2,z129,z3,z4,z5,z225]),(0,[z1,z2,z3,z635,z4,z5,z8]),(0,[z90,z1,z2,z393,z4,z5,z8]),(0,[z1,z2,z3,z102,z4,z5,z8])],[(0,[z636,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z458,z3,z4,z5,z8]),(0,[z289,z1,z2,z3,z4,z5,z252]),(0,[z1,z2,z3,z4,z5,z637,z8]),(0,[z1,z2,z10,z4,z5,z25,z8]),(0,[z1,z2,z3,z4,z63,z5,z8])],[(0,[z1,z2,z638,z3,z4,z5,z8]),(0,[z1,z2,z56,z26,z4,z5,z8]),(0,[z1,z2,z3,z106,z5,z28,z8]),(0,[z72,z1,z2,z294,z4,z5,z8]),(0,[z1,z621,z2,z3,z4,z5,z25])],[(0,[z1,z2,z3,z62,z106,z5,z8]),(0,[z109,z1,z2,z38,z4,z5,z8]),(0,[z1,z2,z3,z4,z639,z5,z8])],[(0,[z640,z1,z2,z3,z4,z5,z8]),(0,[z641,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z28,z8])],[(0,[z642,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z27,z142,z8]),(0,[z1,z2,z3,z4,z5,z8,z316])]],
   [[(0,[z119,z1,z24,z3,z4,z5,z8]),(0,[z1,z290,z2,z3,z4,z5,z8]),(0,[z643,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z31,z4,z5,z8])],[(0,[z69,z1,z18,z3,z4,z5,z8]),(0,[z1,z18,z3,z4,z522,z5,z8]),(0,[z289,z1,z24,z3,z4,z5,z8]),(0,[z1,z24,z10,z3,z4,z5,z8]),(0,[z187,z1,z46,z2,z3,z5,z8]),(0,[z1,z2,z3,z4,z5,z644,z8]),(0,[z109,z1,z2,z4,z5,z8,z12]),(0,[z1,z2,z3,z4,z645,z5,z8]),(0,[z1,z2,z646,z3,z4,z5,z8])],[(0,[z1,z18,z38,z3,z4,z5,z8]),(0,[z389,z1,z24,z3,z4,z5,z8]),(0,[z1,z2,z647,z3,z4,z5,z8]),(0,[z72,z1,z2,z3,z4,z5,z25]),(0,[z1,z2,z3,z4,z81,z5,z12]),(0,[z1,z2,z3,z648,z4,z5,z8])],[(1,[z1,z68,z18,z3,z5,z8]),(1,[z1,z2,z3,z4,z5,z225]),(0,[z1,z2,z3,z4,z45,z142,z8]),(0,[z1,z2,z649,z3,z4,z5,z8]),(1,[z1,z2,z3,z59,z28,z8])],[(0,[z1,z205,z2,z3,z4,z5,z8]),(0,[z109,z1,z2,z3,z410,z5,z8]),(0,[z1,z2,z3,z4,z63,z5,z25])],[(0,[z1,z2,z3,z185,z4,z5,z8]),(0,[z194,z1,z24,z3,z4,z5,z8]),(1,[z119,z2,z129,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z650,z8]),(0,[z1,z2,z3,z4,z5,z5,z8]),(1,[z1,z2,z3,z91,z5,z8]),(0,[z1,z2,z3,z91,z4,z5,z8]),(0,[z1,z2,z651,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z652])],[(0,[z401,z1,z24,z3,z4,z5,z8]),(0,[z37,z1,z2,z3,z4,z27,z8]),(0,[z1,z2,z3,z4,z5,z8,z653]),(0,[z1,z2,z3,z4,z654,z5,z8]),(0,[z1,z2,z655,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z428,z5,z8])],[(0,[z338,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z656,z5,z8]),(0,[z641,z1,z2,z3,z4,z5,z25]),(0,[z1,z2,z3,z4,z5,z28,z25]),(0,[z83,z1,z2,z3,z4,z5,z8])]],
   [[(0,[z1,z344,z2,z3,z4,z5,z8]),(1,[z69,z2,z3,z4,z27,z8]),(0,[z1,z2,z3,z657,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z658,z8])],[(1,[z1,z2,z236,z4,z5,z8]),(0,[z37,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z31,z4,z5,z25])],[(0,[z1,z218,z18,z3,z4,z5,z8]),(0,[z1,z2,z201,z3,z4,z5,z8]),(1,[z53,z2,z3,z106,z5,z8]),(0,[z90,z289,z2,z3,z4,z5,z8]),(0,[z659,z1,z2,z3,z4,z5,z8])],[(0,[z1,z18,z3,z26,z4,z5,z8]),(0,[z69,z119,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z660,z4,z5,z8]),(0,[z1,z2,z3,z4,z661,z5,z8]),(0,[z1,z2,z3,z4,z5,z221,z8]),(1,[z289,z2,z3,z4,z5,z252]),(0,[z130,z1,z2,z176,z4,z5,z8]),(0,[z662,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z663,z4,z5,z8])],[(0,[z1,z18,z11,z3,z4,z5,z8]),(0,[z1,z24,z3,z4,z81,z5,z8]),(0,[z130,z1,z24,z3,z4,z5,z8]),(0,[z1,z664,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z5,z120,z8]),(0,[z1,z2,z3,z665,z4,z5,z8])],[(0,[z1,z2,z129,z3,z4,z5,z513]),(0,[z54,z1,z2,z3,z4,z5,z25]),(0,[z1,z2,z3,z4,z666,z5,z8])],[(0,[z17,z1,z18,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z667]),(0,[z1,z2,z3,z4,z668,z5,z8]),(0,[z72,z1,z2,z3,z4,z5,z12])],[(0,[z1,z18,z3,z4,z5,z8,z70]),(0,[z1,z24,z3,z4,z5,z45,z8]),(0,[z1,z2,z11,z3,z4,z5,z8]),(0,[z1,z42,z2,z176,z4,z5,z8]),(0,[z54,z72,z1,z3,z4,z5,z8]),(0,[z1,z2,z177,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z669]),(0,[z1,z670,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z102,z4,z5,z12])]],
   [[(0,[z1,z42,z24,z3,z4,z5,z8]),(0,[z671,z1,z2,z3,z4,z5,z8]),(0,[z37,z1,z161,z3,z4,z5,z8]),(0,[z1,z46,z2,z3,z5,z8,z103]),(0,[z1,z2,z3,z4,z5,z8,z672]),(0,[z1,z2,z3,z4,z5,z673,z8]),(0,[z1,z2,z3,z4,z63,z5,z12]),(0,[z1,z2,z3,z4,z5,z674,z8]),(0,[z1,z675,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z676,z4,z5,z8])],[(0,[z1,z18,z3,z4,z106,z5,z8]),(0,[z1,z18,z3,z62,z4,z5,z8]),(0,[z1,z170,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z27,z81,z8]),(0,[z90,z72,z1,z2,z3,z4,z5]),(1,[z1,z2,z11,z4,z5,z12]),(0,[z1,z2,z3,z4,z5,z8,z47])],[(1,[z1,z218,z18,z3,z4,z5]),(0,[z1,z2,z3,z4,z677,z5,z8]),(0,[z37,z1,z2,z3,z4,z5,z25]),(0,[z1,z2,z3,z678,z4,z5,z8]),(0,[z679,z1,z2,z3,z4,z5,z8])],[(0,[z65,z1,z2,z3,z4,z5,z8]),(1,[z64,z18,z3,z4,z5,z8]),(0,[z1,z2,z3,z680,z4,z5,z8]),(0,[z1,z2,z3,z4,z681,z5,z8]),(0,[z1,z2,z3,z682,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z78,z12]),(0,[z1,z2,z3,z4,z5,z28,z12]),(0,[z1,z2,z3,z4,z5,z8,z60]),(0,[z1,z2,z3,z31,z4,z140,z8])],[(0,[z683,z1,z2,z3,z4,z5,z8]),(0,[z90,z1,z2,z3,z602,z5,z8]),(0,[z1,z2,z3,z4,z602,z5,z8]),(1,[z1,z2,z3,z4,z5,z316])],[(0,[z684,z1,z2,z3,z4,z5,z8]),(0,[z1,z414,z2,z3,z4,z5,z8]),(1,[z1,z162,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z685,z5,z8]),(0,[z1,z2,z3,z31,z4,z5,z12]),(0,[z1,z2,z3,z4,z5,z8,z686])],[(0,[z65,z24,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z513]),(0,[z1,z2,z687,z3,z4,z5,z8]),(0,[z76,z1,z2,z3,z4,z204,z8]),(0,[z72,z1,z2,z3,z4,z5,z182])],[(0,[z1,z2,z3,z688,z4,z5,z8]),(0,[z689,z1,z2,z3,z4,z5,z8]),(0,[z53,z1,z2,z3,z4,z5,z328]),(0,[z1,z2,z690,z3,z4,z5,z8])]],
   [[(0,[z1,z2,z3,z4,z691,z5,z8]),(0,[z1,z2,z11,z3,z4,z5,z25]),(0,[z72,z1,z2,z3,z4,z140,z5]),(0,[z1,z121,z2,z3,z4,z5,z22]),(0,[z692,z1,z2,z3,z4,z5,z8]),(0,[z39,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z103])],[(0,[z1,z24,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z454]),(0,[z693,z1,z2,z3,z4,z5,z8]),(1,[z1,z2,z4,z81,z5,z12]),(0,[z1,z694,z2,z3,z4,z5,z8])],[(0,[z0,z1,z24,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z695,z8]),(1,[z1,z2,z10,z4,z5,z25])],[(0,[z1,z24,z638,z3,z4,z5,z8]),(0,[z109,z1,z24,z3,z4,z5,z8]),(0,[z1,z2,z3,z696,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z13]),(0,[z1,z2,z697,z3,z4,z5,z8]),(0,[z72,z1,z2,z3,z4,z5,z32])],[(0,[z65,z1,z2,z3,z4,z5,z25]),(0,[z1,z2,z3,z698,z4,z5,z8]),(0,[z1,z2,z699,z3,z4,z5,z8]),(0,[z109,z1,z2,z3,z473,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z617])],[(0,[z1,z2,z3,z4,z385,z5,z8]),(0,[z1,z42,z2,z11,z4,z5,z8]),(0,[z1,z2,z3,z4,z700,z5,z8]),(0,[z191,z1,z2,z4,z160,z5,z8]),(0,[z1,z2,z3,z4,z5,z12,z103]),(0,[z1,z2,z3,z4,z5,z8,z701]),(0,[z1,z702,z2,z3,z4,z5,z8]),(1,[z1,z2,z4,z428,z5,z8])],[(0,[z64,z2,z18,z3,z4,z5,z8]),(0,[z1,z203,z24,z3,z4,z5,z8]),(0,[z37,z1,z2,z3,z4,z5,z12]),(0,[z1,z2,z11,z3,z377,z5,z8]),(0,[z703,z1,z2,z3,z4,z5,z8])],[(0,[z64,z1,z2,z3,z4,z5,z8]),(0,[z1,z24,z3,z31,z4,z5,z8]),(1,[z1,z2,z3,z4,z385,z8]),(0,[z1,z2,z3,z4,z704,z5,z8]),(0,[z1,z2,z3,z4,z705,z5,z8]),(0,[z1,z706,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z31,z4,z140,z5])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z2,z3,z4,z707,z5]),(0,[z1,z2,z3,z4,z310,z197]),(0,[z1,z2,z3,z5,z708,z8]),(0,[z1,z2,z3,z709,z5,z8]),(0,[z1,z2,z134,z4,z5,z12])],[(0,[z1,z150,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z710]),(0,[z1,z2,z3,z106,z5,z328])],[(0,[z1,z18,z3,z4,z34,z8]),(0,[z1,z24,z260,z4,z5,z12]),(0,[z1,z2,z3,z4,z5,z711]),(0,[z109,z1,z48,z4,z5,z12])],[(0,[z39,z18,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z712]),(0,[z1,z288,z3,z4,z5,z12]),(0,[z1,z2,z3,z4,z5,z713]),(0,[z1,z121,z2,z3,z4,z298]),(0,[z1,z2,z3,z4,z5,z74]),(0,[z1,z2,z3,z4,z5,z714])],[(0,[z1,z2,z236,z4,z310,z8]),(0,[z1,z46,z297,z3,z5,z8]),(0,[z289,z1,z2,z294,z4,z5]),(0,[z1,z48,z3,z410,z5,z8]),(0,[z1,z2,z3,z4,z715,z8])],[(0,[z1,z18,z3,z4,z5,z47]),(0,[z53,z2,z3,z106,z310,z8]),(0,[z130,z1,z716,z4,z5,z8]),(0,[z1,z2,z4,z717,z204,z5]),(0,[z1,z255,z3,z4,z5,z211])],[(0,[z1,z24,z3,z4,z5,z328]),(0,[z605,z1,z2,z4,z142,z8]),(0,[z1,z2,z3,z602,z5,z12]),(0,[z72,z1,z3,z4,z5,z587]),(0,[z14,z1,z2,z3,z5,z625])],[(0,[z1,z2,z3,z4,z5,z718])],[(0,[z1,z2,z4,z691,z5,z12]),(0,[z1,z2,z3,z4,z5,z719]),(0,[z37,z2,z3,z4,z45,z12]),(0,[z1,z2,z3,z4,z5,z720])],[(0,[z1,z721,z3,z4,z5,z8]),(0,[z1,z722,z3,z4,z5,z8]),(0,[z723,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z724])],[(0,[z1,z150,z3,z4,z5,z25]),(0,[z1,z725,z3,z4,z5,z8]),(0,[z1,z2,z3,z726,z5,z8]),(0,[z1,z2,z4,z562,z5,z12]),(0,[z1,z2,z3,z59,z28,z8])],[(0,[z17,z72,z1,z3,z5,z8]),(0,[z1,z2,z4,z5,z12,z600])],[(0,[z119,z2,z129,z4,z5,z8]),(0,[z0,z2,z26,z4,z308,z8]),(0,[z1,z2,z3,z4,z5,z197]),(0,[z1,z2,z3,z4,z5,z727]),(0,[z1,z621,z3,z4,z5,z22])],[(0,[z24,z68,z18,z3,z5,z8]),(0,[z1,z162,z245,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z728]),(0,[z76,z1,z3,z4,z123,z8]),(1,[z1,z3,z4,z729,z8]),(0,[z1,z2,z3,z4,z145,z32]),(0,[z1,z2,z71,z4,z5,z25])],[(0,[z1,z24,z3,z5,z8,z730]),(0,[z1,z543,z2,z4,z5,z12])],[(0,[z1,z2,z26,z4,z308,z8]),(0,[z1,z2,z3,z4,z5,z731]),(0,[z1,z2,z3,z4,z5,z732])]],
   [[(0,[z1,z18,z185,z4,z5,z12]),(0,[z1,z2,z3,z733,z5,z8]),(0,[z1,z254,z3,z4,z310,z8]),(0,[z1,z2,z3,z4,z734,z8]),(0,[z1,z2,z3,z4,z5,z735]),(0,[z1,z2,z578,z4,z5,z12]),(0,[z1,z2,z3,z4,z5,z211]),(0,[z1,z3,z736,z4,z5,z8])],[(0,[z1,z2,z3,z737,z5,z8]),(0,[z1,z2,z4,z738,z5,z8]),(0,[z72,z1,z75,z3,z4,z5]),(0,[z1,z739,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z740,z8]),(0,[z18,z3,z4,z459,z5,z8]),(0,[z54,z1,z3,z4,z296,z5]),(0,[z1,z2,z3,z5,z8,z741]),(0,[z1,z2,z3,z198,z5,z182])],[(0,[z61,z1,z3,z160,z5,z8]),(0,[z1,z2,z3,z59,z28,z25]),(0,[z1,z2,z3,z31,z4,z742])],[(0,[z1,z743,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z744]),(1,[z1,z173,z4,z5,z12])],[(0,[z745,z1,z3,z4,z5,z8]),(0,[z119,z2,z129,z4,z5,z25]),(0,[z1,z3,z5,z8,z195,z23]),(0,[z1,z2,z4,z5,z362,z12])],[(0,[z1,z2,z3,z4,z5,z746]),(0,[z1,z150,z3,z4,z5,z12]),(0,[z1,z2,z3,z4,z5,z747]),(0,[z748,z2,z3,z4,z5,z8]),(0,[z1,z2,z484,z4,z5,z25]),(0,[z1,z2,z33,z31,z4,z140])],[(0,[z1,z2,z749,z4,z5,z8]),(0,[z1,z24,z3,z4,z298,z8]),(0,[z1,z750,z3,z4,z5,z8]),(0,[z1,z2,z3,z342,z5,z617])],[(0,[z1,z2,z66,z4,z5,z12]),(0,[z1,z2,z3,z4,z5,z751]),(0,[z1,z3,z4,z5,z8,z752])],[(0,[z1,z18,z3,z141,z5,z8])],[(0,[z1,z2,z3,z4,z753,z8]),(0,[z1,z2,z3,z754,z5,z8])],[(0,[z1,z2,z3,z4,z5,z755]),(0,[z1,z756,z3,z4,z5,z8]),(0,[z1,z2,z757,z4,z296,z5]),(0,[z110,z2,z3,z4,z142,z8])],[(0,[z24,z218,z18,z3,z4,z5]),(0,[z1,z254,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z758,z8]),(0,[z1,z2,z3,z602,z5,z252]),(0,[z1,z759,z3,z4,z5,z8])],[(0,[z1,z2,z3,z760,z5,z8]),(0,[z1,z2,z3,z761,z5,z8]),(0,[z1,z2,z3,z4,z5,z762]),(0,[z1,z763,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z764,z5])],[(0,[z1,z18,z3,z159,z5,z8]),(0,[z17,z1,z3,z5,z590,z8]),(0,[z1,z203,z3,z4,z296,z204]),(0,[z1,z2,z3,z4,z5,z765])],[(0,[z76,z1,z3,z4,z19,z8]),(0,[z1,z2,z3,z59,z28,z12]),(0,[z1,z2,z3,z59,z28,z214])]],
   [[(0,[z1,z2,z3,z4,z5,z766]),(0,[z1,z2,z26,z4,z5,z6]),(0,[z1,z2,z4,z81,z5,z12]),(0,[z1,z750,z3,z4,z5,z25])],[(0,[z61,z1,z3,z102,z5,z8])],[(0,[z1,z18,z3,z767,z5,z8]),(0,[z1,z18,z177,z4,z5,z8]),(0,[z1,z2,z3,z5,z8,z768]),(0,[z1,z24,z3,z602,z5,z8]),(0,[z76,z1,z3,z4,z123,z12]),(0,[z1,z2,z769,z160,z5,z8]),(0,[z1,z2,z3,z4,z5,z770])],[(0,[z1,z18,z3,z4,z5,z771]),(0,[z1,z2,z446,z4,z5,z772])],[(0,[z1,z2,z3,z773,z5,z8]),(0,[z105,z1,z121,z3,z4,z5]),(0,[z2,z26,z4,z45,z142,z8]),(0,[z1,z2,z774,z4,z5,z8]),(0,[z107,z1,z2,z4,z142,z8]),(0,[z1,z2,z3,z4,z5,z775]),(0,[z109,z1,z2,z4,z271,z8])],[(0,[z1,z776,z3,z4,z5,z8]),(0,[z1,z254,z3,z4,z5,z25]),(0,[z1,z46,z2,z3,z5,z328])],[(0,[z1,z2,z3,z777,z5,z8]),(0,[z1,z2,z3,z4,z385,z8]),(0,[z187,z2,z3,z36,z5,z8])],[(0,[z1,z18,z196,z4,z5,z8]),(0,[z1,z18,z3,z102,z5,z182]),(0,[z1,z2,z3,z4,z7,z8]),(0,[z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z11,z377,z5,z12]),(0,[z54,z1,z3,z5,z120,z8])],[(0,[z1,z24,z3,z4,z5,z361]),(0,[z69,z2,z3,z4,z415,z8]),(0,[z1,z2,z3,z4,z5,z778]),(0,[z1,z2,z3,z5,z779,z25])],[(0,[z1,z18,z3,z4,z5,z780]),(0,[z1,z2,z3,z4,z5,z781]),(0,[z1,z2,z3,z782,z5,z8]),(0,[z1,z783,z3,z4,z5,z8])],[(0,[z119,z421,z129,z4,z5,z8]),(0,[z1,z2,z3,z784,z5,z8]),(0,[z109,z1,z173,z4,z142,z8])],[(0,[z1,z288,z3,z188,z5,z8]),(0,[z1,z2,z3,z102,z5,z617]),(0,[z1,z2,z3,z4,z5,z785])],[],[(0,[z1,z2,z635,z4,z5,z12]),(0,[z1,z2,z3,z786,z5,z8]),(0,[z1,z2,z3,z91,z298,z8]),(0,[z1,z621,z3,z4,z5,z425])],[(0,[z105,z1,z18,z787,z4,z5]),(0,[z61,z1,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z788])],[(0,[z1,z2,z218,z68,z3,z5]),(0,[z1,z24,z26,z4,z5,z12]),(0,[z1,z2,z3,z4,z385,z25]),(0,[z187,z170,z3,z36,z5,z8]),(0,[z187,z2,z3,z36,z5,z25]),(0,[z1,z2,z3,z754,z5,z12]),(0,[z1,z2,z3,z4,z5,z60])]],
   [[(0,[z2,z129,z789,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z790]),(0,[z37,z2,z3,z188,z45,z8]),(0,[z1,z2,z3,z4,z7,z25]),(0,[z90,z2,z3,z4,z5,z427])],[(0,[z1,z254,z3,z4,z5,z12]),(0,[z1,z2,z4,z5,z441,z12]),(0,[z1,z2,z4,z171,z5,z12]),(0,[z1,z791,z3,z4,z5,z8])],[(0,[z17,z1,z3,z127,z5,z8]),(0,[z1,z75,z3,z4,z5,z8]),(0,[z90,z2,z3,z91,z5,z70]),(0,[z1,z2,z3,z4,z5,z792]),(0,[z1,z2,z3,z4,z5,z793])],[(0,[z412,z1,z2,z4,z142,z8]),(0,[z1,z2,z3,z4,z310,z8]),(0,[z1,z3,z4,z5,z794,z8])],[(0,[z2,z26,z4,z5,z78,z12]),(0,[z1,z255,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z795,z8]),(0,[z1,z2,z3,z4,z5,z796]),(1,[z1,z716,z4,z5,z8])],[(0,[z105,z1,z273,z3,z4,z5]),(0,[z1,z2,z3,z188,z27,z8]),(0,[z1,z2,z797,z4,z5,z8])],[(0,[z1,z121,z3,z4,z5,z272]),(0,[z109,z39,z2,z4,z142,z8]),(0,[z61,z1,z3,z4,z5,z25])],[(0,[z1,z798,z18,z3,z4,z5]),(0,[z0,z2,z26,z375,z5,z8]),(0,[z1,z88,z236,z4,z5,z8]),(0,[z37,z2,z3,z4,z45,z221]),(0,[z72,z1,z3,z4,z5,z47]),(0,[z1,z2,z799,z4,z5,z8])],[(0,[z1,z2,z800,z4,z5,z8]),(0,[z1,z205,z3,z4,z385,z8]),(0,[z1,z2,z129,z375,z5,z8]),(0,[z53,z88,z3,z106,z5,z8])],[(0,[z1,z18,z3,z4,z16,z32]),(0,[z1,z42,z638,z4,z5,z8]),(0,[z1,z2,z3,z4,z34,z328]),(0,[z1,z2,z3,z5,z801,z8]),(0,[z1,z2,z3,z4,z5,z111])],[(0,[z1,z2,z3,z4,z802,z8]),(0,[z1,z2,z3,z5,z8,z803]),(0,[z1,z24,z3,z59,z28,z8]),(0,[z1,z2,z3,z804,z5,z8]),(0,[z1,z2,z26,z375,z5,z8]),(0,[z1,z2,z3,z4,z385,z12]),(0,[z187,z2,z3,z36,z5,z12]),(0,[z1,z75,z3,z4,z5,z25]),(0,[z1,z48,z3,z4,z5,z325]),(0,[z194,z1,z2,z3,z5,z178]),(0,[z1,z2,z3,z4,z495,z32])],[(0,[z1,z18,z33,z4,z5,z8]),(0,[z1,z2,z236,z106,z5,z8]),(0,[z1,z2,z3,z4,z310,z25]),(0,[z1,z2,z3,z4,z7,z12]),(0,[z54,z1,z3,z207,z5,z8]),(0,[z1,z805,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z806])],[(0,[z1,z2,z3,z5,z807,z8]),(0,[z119,z24,z129,z4,z5,z8]),(0,[z1,z203,z3,z4,z396,z8]),(0,[z54,z1,z3,z179,z5,z8]),(0,[z1,z2,z3,z4,z5,z808]),(0,[z1,z255,z3,z4,z5,z25]),(0,[z109,z1,z48,z4,z142,z8]),(0,[z1,z809,z3,z4,z5,z8])],[(0,[z483,z1,z3,z4,z123,z8]),(0,[z54,z1,z2,z236,z5,z8]),(0,[z1,z2,z446,z4,z45,z8]),(0,[z1,z2,z3,z810,z5,z8])],[(0,[z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z129,z4,z5,z12])]],
   [[(0,[z69,z24,z3,z4,z27,z8]),(0,[z1,z2,z4,z5,z669,z12])],[(0,[z1,z2,z3,z787,z4,z5]),(0,[z1,z24,z236,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z221]),(0,[z1,z2,z4,z428,z5,z182])],[(0,[z53,z24,z3,z106,z5,z8]),(0,[z486,z2,z3,z4,z27,z8]),(0,[z90,z162,z3,z4,z5,z70]),(0,[z1,z2,z811,z3,z4,z5]),(0,[z1,z2,z3,z812,z5,z8])],[(0,[z54,z1,z3,z235,z5,z8]),(0,[z61,z1,z3,z4,z5,z12])],[(0,[z87,z18,z3,z4,z5,z8]),(0,[z813,z1,z2,z3,z5,z8])],[(0,[z1,z18,z814,z4,z5,z8]),(0,[z1,z3,z4,z5,z195,z47])],[(0,[z1,z815,z3,z4,z5,z8]),(0,[z1,z2,z393,z602,z5,z8]),(0,[z54,z1,z3,z179,z5,z25]),(0,[z1,z3,z4,z5,z126,z724])],[(0,[z244,z18,z3,z4,z5,z8]),(0,[z119,z2,z3,z4,z308,z8]),(0,[z1,z2,z3,z206,z28,z8]),(0,[z1,z75,z3,z4,z5,z12]),(0,[z1,z2,z816,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z25]),(0,[z1,z170,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z310,z12]),(0,[z1,z2,z817,z4,z5,z8]),(0,[z508,z1,z176,z4,z5,z8]),(0,[z1,z11,z716,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z818])],[(0,[z1,z173,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z819]),(0,[z1,z2,z820,z4,z5,z8]),(0,[z1,z255,z3,z4,z5,z12])],[],[(0,[z1,z18,z245,z4,z5,z8]),(0,[z105,z1,z68,z18,z3,z5]),(0,[z1,z2,z821,z4,z5,z8]),(0,[z1,z822,z3,z4,z5,z8])],[(0,[z823,z1,z18,z3,z5,z8])],[(0,[z1,z2,z3,z4,z8,z824]),(0,[z1,z2,z3,z4,z5,z374])],[(0,[z1,z24,z3,z4,z5,z513])],[(0,[z1,z288,z3,z471,z5,z8]),(0,[z1,z3,z43,z5,z8,z23]),(0,[z1,z2,z38,z4,z81,z12]),(0,[z295,z1,z2,z4,z5,z12])]],
   [[(0,[z1,z18,z3,z4,z5,z265]),(0,[z1,z2,z129,z4,z308,z8]),(0,[z1,z2,z825,z4,z5,z8])],[(0,[z1,z24,z4,z81,z5,z12]),(0,[z1,z170,z3,z4,z5,z25]),(0,[z1,z826,z3,z4,z5,z8])],[(0,[z1,z205,z3,z4,z5,z8]),(0,[z823,z1,z2,z3,z5,z8]),(0,[z1,z2,z3,z827,z5,z8]),(0,[z1,z2,z3,z36,z34,z8]),(0,[z54,z1,z3,z179,z5,z12]),(0,[z1,z2,z3,z4,z828,z5]),(0,[z1,z173,z3,z4,z5,z25]),(0,[z1,z2,z3,z5,z25,z829]),(0,[z1,z830,z3,z4,z5,z8])],[(0,[z1,z150,z3,z375,z5,z8]),(0,[z30,z2,z3,z106,z5,z8]),(0,[z831,z2,z3,z4,z5,z8]),(0,[z1,z203,z3,z141,z204,z8]),(0,[z1,z2,z3,z832,z5,z8]),(0,[z109,z110,z2,z4,z142,z8])],[(0,[z1,z2,z3,z4,z5,z12]),(0,[z1,z18,z3,z15,z5,z8]),(0,[z1,z2,z3,z4,z833,z8]),(0,[z37,z2,z3,z471,z45,z8]),(0,[z109,z1,z2,z473,z5,z12]),(0,[z1,z2,z3,z4,z5,z834]),(0,[z1,z2,z3,z4,z5,z214])],[(0,[z1,z218,z3,z4,z5,z590])],[(0,[z1,z2,z3,z4,z835,z8]),(0,[z1,z836,z3,z4,z5,z8]),(0,[z1,z2,z4,z35,z5,z12]),(0,[z83,z1,z3,z4,z5,z32])],[(0,[z1,z18,z3,z4,z5,z837]),(0,[z1,z18,z787,z4,z5,z8]),(0,[z1,z24,z3,z4,z385,z8]),(0,[z383,z2,z26,z4,z5,z8]),(0,[z1,z176,z43,z4,z5,z12]),(0,[z1,z173,z3,z4,z5,z325]),(0,[z1,z173,z3,z4,z5,z374])],[(0,[z1,z24,z3,z4,z7,z8]),(0,[z1,z273,z245,z4,z5,z8]),(0,[z1,z2,z3,z4,z838,z5])],[(0,[z1,z2,z3,z529,z28,z8]),(0,[z76,z1,z3,z4,z123,z25]),(0,[z1,z3,z4,z5,z729,z8]),(0,[z1,z2,z3,z410,z5,z8]),(0,[z1,z181,z2,z3,z5,z103])],[(0,[z1,z2,z798,z3,z4,z5]),(0,[z0,z24,z26,z4,z5,z8]),(0,[z2,z129,z26,z4,z5,z12]),(0,[z1,z121,z2,z3,z5,z23])],[(0,[z1,z2,z68,z3,z5,z8]),(0,[z1,z205,z3,z4,z5,z25]),(0,[z1,z839,z3,z4,z5,z8]),(0,[z1,z2,z3,z827,z5,z25])],[(0,[z1,z255,z3,z160,z5,z8]),(0,[z1,z2,z3,z4,z5,z840])],[(0,[z2,z3,z26,z4,z308,z8]),(0,[z1,z2,z3,z4,z385,z6]),(0,[z1,z841,z3,z4,z5,z8]),(0,[z1,z170,z3,z4,z5,z12]),(0,[z508,z1,z176,z4,z5,z12]),(0,[z1,z2,z3,z842,z5,z8]),(0,[z426,z1,z2,z4,z5,z12]),(0,[z1,z670,z2,z160,z5,z8]),(0,[z1,z2,z3,z4,z5,z843])],[(0,[z1,z2,z3,z4,z5,z844]),(0,[z1,z845,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z846]),(0,[z1,z173,z3,z4,z5,z12]),(0,[z163,z1,z3,z4,z5,z362])],[(0,[z1,z2,z4,z5,z77,z12]),(0,[z1,z2,z3,z4,z5,z847])]],
   [[(0,[z481,z1,z185,z4,z5,z8]),(0,[z0,z2,z26,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z29]),(0,[z1,z2,z3,z4,z848,z8]),(0,[z1,z2,z3,z4,z5,z849])],[(0,[z1,z2,z129,z4,z5,z6]),(0,[z1,z2,z3,z4,z850,z8]),(0,[z110,z2,z10,z4,z5,z8])],[(0,[z1,z851,z3,z4,z5,z8]),(0,[z1,z852,z3,z4,z5,z8]),(0,[z1,z2,z3,z410,z5,z25])],[(0,[z1,z853,z3,z4,z5,z8]),(0,[z1,z173,z3,z410,z5,z8]),(0,[z1,z2,z4,z5,z12,z169])],[(0,[z194,z1,z18,z3,z5,z103]),(0,[z505,z2,z129,z4,z5,z8]),(0,[z1,z3,z4,z5,z854,z8])],[(0,[z1,z2,z3,z4,z308,z8]),(0,[z2,z3,z4,z855,z5,z8]),(0,[z1,z2,z3,z4,z5,z856]),(0,[z1,z2,z3,z5,z857,z8]),(0,[z1,z3,z4,z5,z25,z195]),(0,[z1,z2,z3,z4,z5,z858])],[(0,[z1,z841,z3,z4,z5,z25])],[(0,[z1,z88,z3,z4,z5,z8]),(0,[z1,z18,z201,z4,z5,z12]),(0,[z37,z24,z3,z4,z45,z8]),(0,[z1,z205,z3,z4,z5,z12]),(0,[z1,z2,z3,z410,z5,z374])],[(0,[z1,z2,z3,z859,z5,z8])],[(0,[z1,z18,z3,z377,z5,z8]),(0,[z345,z1,z2,z160,z5,z8]),(0,[z1,z2,z245,z4,z5,z555])],[(0,[z1,z18,z3,z4,z5,z328]),(0,[z1,z860,z3,z4,z5,z8]),(0,[z1,z150,z3,z4,z308,z8]),(0,[z1,z2,z3,z4,z5,z861]),(0,[z1,z2,z3,z862,z5,z8]),(0,[z1,z2,z3,z4,z5,z863]),(0,[z194,z1,z2,z3,z5,z103])],[(0,[z1,z24,z3,z4,z5,z111]),(0,[z1,z2,z3,z226,z28,z8])],[(0,[z1,z2,z3,z864,z5,z8]),(0,[z1,z24,z3,z804,z5,z8]),(0,[z1,z2,z865,z3,z4,z5]),(0,[z1,z866,z3,z4,z5,z8])],[(0,[z1,z24,z3,z867,z5,z8]),(0,[z1,z2,z3,z4,z5,z868]),(0,[z1,z2,z3,z59,z869,z8])],[(0,[z1,z2,z3,z4,z308,z25]),(0,[z1,z46,z2,z236,z5,z8]),(0,[z1,z2,z3,z870,z5,z8]),(0,[z1,z2,z3,z410,z5,z12])],[(0,[z1,z871,z3,z4,z5,z8]),(0,[z1,z2,z18,z787,z4,z5]),(0,[z1,z2,z4,z148,z5,z12]),(0,[z872,z1,z219,z3,z4,z5]),(0,[z1,z2,z3,z5,z588,z103]),(0,[z1,z3,z4,z204,z327,z8]),(0,[z1,z873,z3,z4,z5,z8]),(0,[z1,z563,z3,z4,z5,z216])]],
   [[(0,[z1,z18,z3,z874,z5,z8]),(0,[z1,z2,z68,z3,z5,z12]),(0,[z1,z24,z129,z4,z5,z12]),(0,[z1,z875,z3,z4,z5,z8])],[(0,[z1,z2,z876,z4,z5,z8])],[(0,[z1,z421,z3,z4,z5,z12]),(0,[z1,z2,z3,z5,z304,z8])],[(0,[z1,z2,z3,z4,z5,z877]),(0,[z1,z878,z3,z4,z5,z8]),(0,[z1,z879,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z880,z5])],[(0,[z1,z881,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z882]),(0,[z1,z883,z3,z4,z5,z8])],[(0,[z1,z3,z4,z5,z884,z8]),(0,[z1,z2,z3,z4,z885,z8]),(0,[z1,z2,z3,z886,z5,z12])],[(0,[z1,z24,z3,z4,z5,z712]),(0,[z1,z24,z3,z4,z5,z74]),(0,[z1,z2,z3,z5,z887,z8]),(0,[z1,z88,z3,z4,z5,z197]),(0,[z1,z2,z3,z888,z5,z8]),(0,[z889,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z314]),(0,[z1,z2,z3,z4,z890,z8]),(0,[z1,z2,z301,z4,z5,z12])],[(0,[z1,z205,z3,z4,z308,z8]),(0,[z1,z2,z3,z375,z385,z8]),(0,[z1,z891,z3,z4,z5,z8])],[(0,[z1,z2,z892,z4,z5,z8]),(0,[z24,z463,z3,z4,z5,z8]),(0,[z336,z2,z3,z106,z5,z8])],[(0,[z1,z93,z3,z4,z204,z8]),(0,[z1,z2,z3,z4,z308,z12]),(0,[z1,z893,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z894]),(0,[z1,z2,z3,z4,z5,z895]),(0,[z1,z2,z896,z4,z5,z8]),(0,[z1,z2,z294,z4,z5,z103]),(0,[z1,z2,z3,z431,z5,z556])],[(0,[z1,z18,z3,z4,z298,z8]),(0,[z1,z2,z3,z4,z5,z897]),(0,[z1,z150,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z898]),(0,[z1,z2,z3,z5,z304,z25])],[(0,[z1,z18,z3,z899,z5,z8]),(0,[z1,z88,z3,z4,z5,z12]),(0,[z1,z2,z3,z188,z5,z8]),(0,[z1,z2,z393,z4,z7,z8]),(0,[z1,z3,z4,z5,z126,z8]),(0,[z900,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z901]),(0,[z1,z902,z3,z4,z5,z8]),(0,[z1,z79,z11,z4,z5,z8]),(0,[z1,z121,z3,z4,z5,z903]),(0,[z1,z2,z3,z4,z5,z904])],[(0,[z1,z905,z3,z4,z5,z8]),(0,[z1,z2,z3,z188,z5,z221])],[(0,[z1,z2,z3,z4,z906,z8]),(0,[z1,z2,z213,z4,z5,z12])]],
   [[(0,[z90,z18,z3,z4,z5,z70]),(0,[z17,z1,z3,z185,z5,z8]),(0,[z1,z24,z3,z4,z5,z197]),(0,[z1,z162,z3,z4,z298,z8]),(0,[z1,z2,z3,z4,z532,z32]),(1,[z110,z2,z4,z5,z12]),(0,[z1,z3,z4,z5,z8,z907])],[(0,[z1,z332,z11,z4,z5,z8]),(0,[z594,z24,z3,z4,z5,z8]),(0,[z54,z1,z3,z552,z5,z8]),(0,[z1,z2,z222,z4,z5,z12]),(0,[z1,z2,z908,z4,z5,z8])],[(0,[z1,z2,z26,z4,z5,z316]),(0,[z1,z909,z3,z4,z5,z8]),(0,[z1,z2,z910,z4,z5,z8])],[(0,[z1,z2,z3,z239,z5,z8]),(0,[z911,z1,z3,z4,z5,z8])],[(0,[z1,z24,z3,z4,z5,z211]),(0,[z1,z2,z3,z159,z5,z52]),(0,[z1,z2,z4,z5,z225,z12]),(0,[z1,z2,z176,z4,z5,z12]),(0,[z109,z1,z2,z4,z81,z12])],[(0,[z1,z24,z3,z4,z5,z12]),(0,[z17,z1,z3,z176,z5,z8]),(0,[z1,z24,z3,z4,z5,z214]),(0,[z1,z2,z3,z188,z5,z25]),(0,[z1,z2,z3,z4,z45,z454]),(0,[z1,z2,z3,z4,z912,z8]),(0,[z1,z2,z294,z4,z5,z8]),(0,[z1,z2,z4,z5,z913,z12]),(0,[z1,z875,z3,z4,z5,z12]),(0,[z83,z194,z1,z3,z5,z103])],[(0,[z17,z1,z3,z179,z5,z8]),(0,[z1,z2,z3,z4,z5,z914])],[(0,[z1,z2,z3,z5,z915,z8]),(0,[z1,z2,z3,z5,z304,z12])],[(0,[z1,z288,z446,z4,z5,z8]),(0,[z1,z2,z3,z4,z906,z25])],[(0,[z1,z2,z3,z4,z5,z916]),(0,[z1,z3,z43,z709,z5,z8]),(0,[z1,z3,z4,z5,z917,z8])],[(0,[z1,z2,z3,z4,z5,z918]),(0,[z72,z1,z3,z4,z5,z137])],[(0,[z1,z2,z3,z4,z5,z919]),(0,[z1,z162,z3,z602,z5,z8]),(0,[z1,z42,z21,z4,z5,z8])],[(0,[z1,z18,z3,z473,z5,z8]),(0,[z1,z2,z3,z4,z5,z920]),(0,[z1,z288,z3,z4,z5,z454]),(0,[z2,z3,z446,z4,z45,z8]),(0,[z1,z2,z3,z239,z5,z25]),(0,[z76,z1,z3,z4,z550,z8])],[(0,[z37,z2,z446,z4,z45,z8]),(0,[z1,z2,z4,z921,z5,z8]),(0,[z90,z273,z3,z4,z5,z70]),(0,[z83,z1,z3,z5,z28,z8])],[(0,[z130,z1,z260,z4,z5,z8]),(0,[z618,z1,z2,z160,z5,z8]),(0,[z1,z288,z458,z4,z5,z8]),(0,[z1,z2,z3,z922,z5,z8]),(0,[z1,z2,z294,z4,z5,z25]),(0,[z1,z923,z3,z4,z5,z8]),(0,[z109,z1,z2,z4,z5,z74])],[(0,[z2,z26,z4,z5,z308,z8]),(0,[z614,z1,z2,z4,z5,z12]),(0,[z109,z1,z2,z473,z142,z8]),(0,[z1,z924,z3,z4,z5,z8])]],
   [[(0,[z1,z2,z3,z4,z5,z925]),(0,[z1,z121,z2,z4,z428,z5]),(0,[z926,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z325])],[(0,[z1,z2,z3,z375,z5,z8]),(0,[z1,z2,z3,z188,z5,z12]),(0,[z37,z2,z3,z4,z45,z454]),(0,[z1,z3,z4,z5,z126,z12])],[(0,[z1,z927,z3,z4,z5,z8]),(0,[z1,z2,z3,z928,z5,z8])],[(0,[z1,z18,z3,z4,z5,z491]),(0,[z1,z2,z446,z4,z27,z8]),(0,[z37,z2,z458,z4,z45,z8]),(0,[z929,z1,z3,z4,z5,z8]),(0,[z1,z2,z276,z4,z5,z12]),(0,[z1,z2,z3,z406,z5,z103])],[(0,[z1,z2,z393,z4,z5,z8]),(0,[z1,z930,z3,z4,z5,z8]),(0,[z119,z2,z129,z4,z5,z225]),(0,[z72,z1,z3,z4,z5,z306]),(0,[z1,z2,z931,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z932]),(0,[z1,z2,z3,z4,z742,z8])],[(0,[z187,z2,z3,z855,z5,z8]),(0,[z1,z933,z3,z4,z5,z8]),(0,[z1,z934,z3,z4,z5,z8])],[(0,[z1,z2,z38,z4,z691,z8]),(0,[z1,z2,z3,z935,z5,z8]),(0,[z500,z1,z2,z4,z5,z12]),(0,[z1,z2,z4,z890,z142,z8])],[(0,[z1,z3,z4,z5,z8,z936]),(0,[z1,z2,z3,z4,z27,z454]),(0,[z191,z1,z2,z160,z5,z265]),(0,[z1,z909,z3,z4,z5,z12])],[(0,[z1,z18,z3,z4,z5,z52]),(0,[z1,z18,z3,z937,z4,z5]),(0,[z392,z1,z260,z4,z5,z8]),(0,[z1,z2,z3,z239,z5,z12]),(0,[z911,z1,z3,z4,z5,z12])],[(0,[z90,z2,z245,z4,z5,z70]),(0,[z1,z2,z3,z4,z5,z938]),(0,[z1,z2,z3,z4,z5,z939])],[(0,[z187,z24,z3,z36,z5,z8]),(0,[z1,z2,z3,z375,z5,z25]),(0,[z1,z2,z294,z4,z5,z12]),(0,[z1,z2,z3,z940,z5,z8])],[(0,[z1,z40,z638,z4,z5,z8]),(0,[z1,z24,z3,z4,z5,z9]),(0,[z2,z446,z4,z5,z45,z8]),(0,[z941,z1,z238,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z942]),(0,[z1,z943,z3,z4,z5,z8]),(0,[z1,z2,z3,z944,z5,z8])],[(0,[z1,z2,z3,z4,z5,z945]),(0,[z1,z2,z3,z4,z5,z131]),(0,[z109,z1,z2,z4,z5,z834])],[(0,[z1,z2,z393,z4,z5,z25]),(0,[z1,z46,z3,z43,z5,z8]),(0,[z1,z2,z4,z5,z474,z12])],[(0,[z1,z18,z3,z5,z8,z23]),(0,[z1,z88,z3,z4,z310,z8]),(0,[z1,z933,z3,z4,z5,z25])],[(0,[z1,z2,z3,z15,z16,z32])]],
   [[(0,[z1,z421,z3,z4,z5,z8]),(0,[z1,z18,z3,z946,z4,z5]),(0,[z17,z105,z1,z2,z3,z5]),(0,[z1,z2,z3,z471,z5,z8]),(0,[z947,z1,z3,z4,z5,z8]),(0,[z39,z2,z3,z473,z5,z8]),(0,[z1,z2,z3,z4,z742,z5])],[(0,[z948,z1,z238,z3,z5,z8]),(0,[z1,z2,z3,z949,z5,z8])],[(0,[z1,z2,z196,z4,z5,z328]),(0,[z1,z950,z3,z4,z5,z8]),(0,[z1,z2,z3,z5,z8,z951])],[(0,[z110,z18,z3,z4,z5,z8]),(0,[z1,z2,z3,z952,z4,z5]),(0,[z1,z24,z3,z4,z5,z60]),(0,[z1,z24,z3,z5,z304,z8]),(0,[z1,z953,z3,z4,z5,z8]),(0,[z1,z954,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z955]),(0,[z1,z205,z3,z375,z5,z8]),(0,[z1,z2,z3,z239,z5,z29]),(0,[z1,z2,z294,z4,z140,z5]),(0,[z1,z2,z3,z886,z5,z8])],[(0,[z1,z2,z956,z4,z5,z8]),(0,[z194,z1,z24,z3,z5,z103]),(0,[z1,z2,z957,z4,z5,z8]),(0,[z1,z958,z3,z4,z5,z8]),(0,[z1,z959,z3,z4,z5,z8]),(0,[z1,z2,z520,z4,z5,z25])],[(0,[z624,z18,z3,z4,z5,z8]),(0,[z24,z697,z3,z4,z5,z8]),(0,[z1,z2,z3,z375,z5,z12]),(0,[z1,z46,z3,z43,z5,z25]),(0,[z960,z2,z3,z4,z5,z8]),(0,[z1,z961,z3,z4,z5,z8])],[(0,[z1,z2,z68,z3,z5,z25]),(0,[z1,z24,z3,z4,z310,z8]),(0,[z1,z2,z3,z962,z5,z8]),(0,[z1,z963,z3,z4,z5,z8]),(0,[z1,z2,z3,z5,z964,z8]),(0,[z1,z2,z3,z4,z5,z965])],[(0,[z2,z3,z4,z966,z45,z8]),(0,[z1,z121,z2,z245,z4,z5])],[(0,[z1,z421,z3,z4,z5,z25]),(0,[z1,z2,z3,z471,z5,z25]),(0,[z1,z2,z393,z4,z5,z12]),(0,[z289,z290,z3,z4,z5,z252]),(0,[z39,z967,z3,z4,z5,z8]),(0,[z1,z2,z3,z431,z5,z182])],[(0,[z1,z2,z3,z968,z5,z8]),(0,[z1,z2,z3,z410,z5,z325])],[(0,[z72,z1,z3,z4,z5,z362])],[(0,[z1,z24,z3,z4,z5,z897]),(0,[z1,z969,z3,z4,z5,z8]),(0,[z69,z2,z446,z4,z5,z8]),(0,[z1,z2,z3,z31,z4,z251])],[(0,[z1,z24,z3,z188,z5,z8]),(0,[z289,z2,z3,z4,z5,z78]),(0,[z391,z1,z2,z3,z5,z103])],[],[(0,[z1,z2,z970,z4,z5,z8]),(0,[z971,z2,z3,z4,z5,z8]),(0,[z1,z972,z3,z4,z5,z8]),(0,[z1,z2,z3,z940,z5,z12])]],
   [[(0,[z1,z973,z219,z3,z5,z8]),(0,[z1,z2,z4,z5,z25,z12])],[(0,[z1,z974,z3,z4,z5,z8]),(0,[z1,z2,z3,z91,z7,z8]),(0,[z1,z2,z3,z4,z5,z975])],[(0,[z1,z18,z3,z4,z5,z513]),(0,[z1,z46,z3,z43,z5,z12]),(0,[z1,z121,z3,z4,z5,z216])],[(0,[z1,z24,z3,z4,z5,z8]),(0,[z1,z88,z3,z4,z5,z25]),(0,[z1,z2,z4,z5,z427,z12]),(0,[z1,z976,z3,z4,z5,z8])],[(0,[z1,z2,z3,z977,z5,z8]),(0,[z1,z978,z3,z4,z5,z8])],[(0,[z1,z18,z3,z979,z4,z8]),(0,[z1,z18,z3,z4,z5,z980]),(0,[z1,z24,z3,z4,z5,z221]),(0,[z813,z1,z219,z3,z5,z8]),(0,[z1,z2,z3,z471,z5,z12]),(0,[z1,z2,z4,z5,z843,z12]),(0,[z1,z2,z3,z31,z4,z465])],[(0,[z1,z24,z294,z4,z5,z8]),(0,[z1,z2,z560,z57,z5,z8])],[(0,[z1,z2,z3,z375,z308,z8]),(0,[z1,z2,z3,z981,z5,z8])],[(0,[z1,z2,z3,z4,z982,z8]),(0,[z1,z2,z236,z4,z34,z8])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z53,z2,z3,z106,z34,z8]),(0,[z1,z2,z4,z5,z25,z843])],[(0,[z1,z983,z3,z4,z5,z8]),(0,[z1,z2,z3,z657,z4,z140]),(0,[z1,z2,z3,z4,z5,z984]),(0,[z1,z2,z3,z16,z304,z32])],[(0,[z1,z2,z3,z4,z5,z985]),(1,[z2,z789,z4,z5,z8]),(0,[z986,z2,z3,z4,z5,z8]),(0,[z54,z1,z3,z540,z5,z8]),(0,[z1,z2,z987,z4,z5,z8])],[(0,[z1,z24,z3,z4,z5,z25]),(0,[z1,z2,z3,z988,z5,z8]),(0,[z1,z2,z3,z4,z5,z989])],[(0,[z1,z2,z3,z4,z5,z990]),(0,[z370,z24,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z913]),(0,[z1,z42,z11,z377,z5,z8]),(0,[z1,z2,z3,z253,z5,z8])],[(0,[z0,z18,z26,z4,z5,z8]),(0,[z289,z2,z3,z4,z5,z747])],[(0,[z1,z24,z821,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z991])]],
   [[(0,[z992,z1,z18,z3,z4,z5]),(0,[z1,z121,z273,z3,z4,z5]),(0,[z1,z2,z387,z4,z5,z12]),(0,[z1,z2,z3,z5,z8,z993]),(0,[z61,z1,z3,z57,z5,z8]),(0,[z1,z2,z134,z57,z5,z8])],[(0,[z1,z18,z3,z994,z5,z8]),(0,[z1,z24,z3,z4,z5,z925]),(0,[z1,z24,z3,z4,z5,z325]),(0,[z1,z24,z3,z4,z5,z374]),(0,[z995,z1,z297,z3,z4,z5]),(0,[z1,z162,z3,z4,z7,z8]),(0,[z1,z2,z3,z4,z5,z996])],[(0,[z1,z24,z3,z375,z5,z8]),(0,[z1,z2,z3,z4,z5,z997]),(0,[z289,z75,z3,z4,z5,z252])],[(0,[z1,z2,z129,z4,z5,z316]),(0,[z1,z2,z56,z57,z5,z211]),(0,[z1,z2,z3,z869,z5,z8]),(0,[z1,z998,z3,z4,z5,z8])],[(0,[z1,z254,z3,z4,z34,z8]),(0,[z1,z999,z238,z3,z5,z8]),(0,[z1,z203,z3,z4,z668,z8]),(0,[z1000,z2,z3,z4,z5,z8]),(0,[z1,z2,z646,z4,z5,z25])],[(0,[z1,z2,z400,z4,z5,z12]),(0,[z72,z1,z2,z3,z4,z298]),(0,[z1,z2,z3,z577,z5,z182]),(0,[z1,z1001,z3,z4,z5,z8])],[(0,[z992,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z376,z32]),(0,[z1,z2,z3,z253,z5,z25]),(0,[z515,z2,z3,z4,z5,z470])],[],[(0,[z1,z218,z68,z18,z3,z5]),(0,[z1,z2,z3,z4,z5,z1002]),(0,[z1,z2,z408,z4,z5,z12]),(0,[z1,z2,z4,z5,z565,z12]),(0,[z1,z3,z4,z5,z126,z25]),(0,[z1,z3,z4,z1003,z5,z8])],[(0,[z1,z18,z3,z602,z5,z8]),(0,[z17,z1,z46,z3,z5,z8]),(0,[z72,z1,z3,z4,z5,z443]),(0,[z1,z2,z3,z1004,z5,z8]),(0,[z1,z2,z3,z91,z5,z8]),(0,[z90,z2,z3,z4,z298,z70]),(0,[z72,z1,z3,z4,z608,z5]),(0,[z1,z1005,z3,z4,z5,z8])],[(0,[z1,z2,z416,z4,z5,z12]),(0,[z1,z2,z3,z1006,z5,z8])],[(0,[z37,z18,z3,z4,z45,z8]),(0,[z1,z2,z270,z4,z5,z12]),(1,[z2,z3,z4,z966,z8]),(0,[z1,z273,z3,z4,z298,z8])],[(0,[z1,z1007,z3,z4,z5,z8]),(0,[z1,z205,z3,z4,z5,z6]),(0,[z1,z2,z94,z4,z5,z25])],[(0,[z1,z2,z3,z1008,z5,z8]),(0,[z1,z24,z3,z410,z5,z8]),(0,[z1,z2,z4,z5,z425,z12]),(0,[z508,z1,z3,z4,z5,z13])],[(0,[z442,z18,z3,z4,z5,z8]),(0,[z275,z24,z3,z4,z5,z8]),(0,[z1,z2,z1009,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1010])],[(0,[z64,z17,z18,z3,z5,z8]),(0,[z1,z24,z68,z3,z5,z8]),(0,[z1,z18,z3,z4,z5,z361]),(0,[z1,z2,z3,z4,z5,z1011]),(0,[z1,z1012,z3,z4,z5,z8]),(0,[z1,z42,z560,z4,z5,z8]),(0,[z76,z1,z3,z4,z729,z8])]],
   [[(0,[z1,z2,z4,z428,z5,z70]),(0,[z72,z1,z294,z4,z5,z137])],[(0,[z1,z2,z3,z4,z1013,z5]),(0,[z1,z3,z4,z729,z123,z8]),(0,[z1,z2,z3,z156,z5,z182])],[(0,[z603,z2,z26,z4,z5,z8]),(0,[z1,z2,z3,z91,z5,z25]),(0,[z1,z2,z3,z253,z5,z12])],[(0,[z1,z2,z446,z188,z5,z8]),(0,[z2,z3,z4,z5,z966,z8]),(0,[z1,z2,z3,z4,z5,z1014]),(0,[z1,z2,z4,z5,z593,z12]),(0,[z1,z2,z3,z1015,z5,z8])],[(0,[z1,z24,z3,z4,z5,z29]),(0,[z1,z2,z3,z4,z5,z1016]),(0,[z1,z203,z176,z4,z5,z12]),(0,[z1,z1017,z3,z4,z5,z8])],[(0,[z132,z24,z3,z4,z5,z8]),(0,[z1,z24,z3,z4,z5,z955]),(0,[z1018,z1,z2,z4,z5,z8]),(0,[z1,z865,z297,z3,z4,z5]),(0,[z1,z2,z11,z4,z5,z12]),(0,[z54,z1,z3,z595,z5,z8]),(0,[z1,z3,z4,z5,z22,z903])],[(0,[z1,z18,z26,z4,z5,z12]),(0,[z72,z1,z218,z3,z4,z5]),(0,[z1,z2,z4,z5,z1019,z8]),(0,[z1,z273,z3,z602,z5,z8]),(0,[z39,z48,z3,z4,z5,z8])],[(0,[z64,z18,z3,z4,z5,z8]),(0,[z1,z2,z245,z4,z298,z8]),(0,[z1,z2,z56,z769,z5,z8])],[(0,[z1,z2,z3,z4,z5,z1020]),(0,[z1,z2,z3,z4,z5,z1021]),(0,[z228,z1,z2,z3,z5,z103]),(0,[z1022,z1,z2,z3,z5,z8]),(0,[z1,z2,z3,z4,z1023,z8])],[(0,[z109,z1,z18,z4,z5,z12]),(0,[z1,z24,z3,z4,z308,z8]),(0,[z1,z2,z446,z4,z5,z8]),(0,[z1,z2,z1024,z4,z5,z8])],[(0,[z54,z1,z3,z5,z8,z23])],[(0,[z105,z1,z3,z499,z4,z5]),(0,[z1,z2,z446,z4,z5,z221])],[(0,[z1,z24,z3,z859,z5,z8]),(0,[z662,z2,z129,z4,z5,z8]),(0,[z1,z2,z196,z4,z5,z1025])],[(0,[z18,z3,z4,z99,z5,z8]),(0,[z1,z2,z3,z4,z5,z454]),(0,[z1,z2,z3,z5,z1026,z8]),(0,[z1,z2,z3,z5,z25,z23]),(0,[z1,z3,z4,z5,z1027,z8])],[(0,[z53,z2,z196,z106,z5,z8]),(0,[z1,z2,z3,z91,z5,z12]),(0,[z1,z1028,z3,z4,z5,z8])],[(0,[z1,z2,z3,z1029,z5,z8]),(0,[z1,z2,z458,z4,z5,z8]),(0,[z1,z2,z3,z4,z308,z6]),(0,[z220,z2,z3,z4,z45,z8]),(0,[z109,z1,z2,z4,z5,z12])]],
   [[(0,[z64,z18,z3,z4,z5,z25]),(0,[z1,z2,z3,z4,z5,z1030]),(0,[z1,z3,z4,z5,z903,z137])],[(0,[z1,z24,z4,z5,z25,z12]),(0,[z1,z2,z458,z4,z5,z221]),(0,[z1,z2,z4,z5,z480,z12]),(0,[z1,z2,z3,z4,z1023,z25]),(0,[z1,z1031,z3,z4,z5,z8])],[(0,[z1,z18,z3,z59,z28,z8]),(0,[z1,z2,z446,z4,z5,z25]),(0,[z110,z2,z4,z5,z8,z12]),(0,[z1,z1032,z3,z4,z5,z8])],[(0,[z1,z46,z3,z135,z5,z8]),(0,[z1,z2,z3,z4,z5,z1033]),(0,[z1,z1034,z3,z4,z5,z8])],[(0,[z119,z18,z129,z4,z5,z8]),(0,[z1,z18,z3,z4,z5,z197]),(0,[z208,z18,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z1035,z8]),(0,[z61,z1,z3,z5,z8,z103])],[(0,[z17,z1,z18,z3,z5,z8]),(0,[z1,z2,z4,z5,z1036,z8]),(0,[z1,z2,z3,z471,z5,z221]),(0,[z54,z1,z3,z5,z126,z8]),(0,[z1,z2,z3,z4,z5,z1037])],[(0,[z330,z18,z3,z4,z5,z8]),(0,[z515,z2,z26,z4,z5,z8]),(0,[z1,z1038,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z1039,z5]),(0,[z1,z2,z4,z488,z5,z12]),(0,[z1,z3,z232,z4,z5,z211])],[(0,[z69,z18,z3,z4,z27,z8]),(0,[z1,z2,z3,z4,z34,z8]),(0,[z1,z255,z56,z57,z5,z8]),(0,[z497,z2,z3,z4,z5,z78])],[(0,[z1,z18,z236,z4,z5,z8]),(0,[z1,z18,z3,z4,z5,z211]),(0,[z1,z2,z458,z4,z5,z25])],[(0,[z1,z2,z3,z1040,z5,z8]),(0,[z53,z18,z3,z106,z5,z8]),(0,[z1,z2,z3,z4,z1041,z5]),(0,[z1,z1042,z238,z3,z4,z5]),(0,[z1,z1043,z3,z4,z5,z8])],[(0,[z1,z24,z3,z4,z5,z6]),(0,[z1,z2,z3,z159,z385,z8])],[(0,[z17,z1,z2,z3,z5,z8]),(0,[z1,z2,z3,z4,z1044,z8]),(0,[z1,z24,z3,z5,z887,z8]),(0,[z1,z24,z3,z4,z5,z314]),(0,[z1,z2,z3,z4,z5,z1045])],[(0,[z64,z18,z3,z4,z5,z12]),(0,[z1,z490,z3,z135,z5,z8]),(0,[z1,z2,z3,z4,z5,z293])],[(0,[z1,z218,z3,z4,z5,z22]),(0,[z0,z2,z26,z159,z5,z8]),(0,[z72,z1,z3,z4,z5,z195]),(0,[z1,z2,z4,z639,z5,z12])],[(0,[z1,z18,z3,z4,z5,z746]),(0,[z17,z1,z18,z3,z5,z25]),(0,[z1046,z1,z18,z3,z4,z5]),(0,[z1047,z1,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z1048,z5]),(0,[z1,z24,z3,z253,z5,z8]),(0,[z1,z2,z446,z4,z5,z12]),(0,[z1,z162,z3,z4,z5,z12]),(0,[z1,z3,z4,z709,z5,z8]),(0,[z1,z2,z3,z4,z5,z1049]),(0,[z1,z2,z4,z428,z16,z5])],[(0,[z559,z18,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1050]),(0,[z1,z2,z4,z5,z1051,z12]),(0,[z613,z1,z2,z3,z5,z103])]],
   [[(0,[z17,z105,z1,z3,z5,z8]),(0,[z1,z2,z3,z4,z34,z25]),(0,[z628,z1,z2,z3,z5,z103])],[(0,[z1,z2,z3,z1052,z5,z8]),(0,[z1,z2,z3,z4,z1053,z8]),(0,[z1,z2,z3,z4,z1054,z8]),(0,[z1,z2,z3,z1055,z5,z8]),(0,[z1,z2,z3,z31,z4,z140])],[(0,[z1,z2,z3,z1056,z5,z8]),(0,[z1,z2,z3,z4,z5,z1057]),(0,[z1058,z2,z3,z4,z5,z8]),(0,[z1,z3,z5,z126,z120,z8]),(0,[z1,z2,z56,z57,z5,z8])],[(0,[z1,z1059,z3,z4,z5,z8]),(1,[z1,z3,z4,z5,z903]),(0,[z1,z2,z3,z4,z5,z1060])],[(0,[z17,z1,z3,z204,z5,z8]),(0,[z17,z1,z2,z3,z5,z25]),(0,[z1046,z1,z2,z3,z4,z5]),(0,[z1,z1061,z3,z4,z5,z8]),(0,[z1,z2,z458,z4,z5,z12]),(0,[z1,z2,z3,z213,z4,z489])],[(0,[z1,z18,z3,z760,z5,z8]),(0,[z1,z2,z3,z4,z5,z1062]),(0,[z1,z2,z3,z4,z459,z32])],[(0,[z1,z2,z372,z4,z5,z12])],[(0,[z1,z2,z3,z1063,z5,z8]),(0,[z1,z24,z3,z239,z5,z8]),(0,[z1,z2,z3,z4,z34,z197]),(0,[z1,z2,z294,z4,z5,z22]),(0,[z1,z2,z3,z4,z1064,z5])],[(0,[z1,z18,z4,z81,z5,z12]),(0,[z1,z24,z176,z4,z5,z12]),(0,[z1,z1065,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z1066,z5])],[(0,[z1,z2,z3,z769,z5,z8]),(0,[z109,z1,z2,z410,z5,z12])],[(0,[z1,z2,z3,z4,z1067,z8]),(0,[z17,z1,z18,z3,z5,z12]),(0,[z1,z18,z3,z5,z8,z768]),(0,[z2,z789,z26,z4,z5,z8]),(0,[z37,z161,z3,z4,z45,z8]),(0,[z1,z2,z3,z4,z5,z1068]),(0,[z1,z2,z3,z1055,z5,z25])],[(0,[z1069,z1,z18,z3,z4,z5]),(0,[z17,z1,z3,z522,z5,z8]),(0,[z515,z2,z26,z4,z5,z12]),(0,[z1,z2,z56,z57,z5,z25])],[(0,[z54,z105,z1,z3,z4,z5]),(0,[z1,z2,z3,z4,z34,z12]),(0,[z1070,z1,z3,z4,z5,z8])],[(0,[z1,z2,z3,z36,z5,z328]),(0,[z411,z2,z3,z4,z45,z8]),(0,[z1,z2,z3,z4,z717,z5]),(0,[z110,z2,z3,z473,z5,z8]),(0,[z200,z1,z2,z4,z5,z12])],[(0,[z1,z18,z3,z4,z385,z8]),(0,[z1,z1071,z3,z4,z5,z8]),(0,[z1,z18,z3,z777,z5,z8]),(0,[z1,z1072,z3,z4,z5,z8]),(0,[z1073,z1,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z296,z5]),(0,[z610,z1,z2,z4,z5,z12]),(1,[z110,z2,z4,z142,z8])],[(0,[z1,z18,z3,z4,z7,z8]),(0,[z1,z18,z3,z4,z5,z9]),(0,[z1,z68,z297,z3,z5,z8]),(0,[z411,z2,z26,z4,z5,z8])]],
   [[(1,[z17,z105,z1,z3,z5]),(0,[z17,z1,z2,z3,z5,z12]),(0,[z1,z1074,z3,z4,z5,z8]),(1,[z2,z3,z855,z5,z8])],[(0,[z1069,z1,z2,z3,z4,z5]),(0,[z1,z2,z1075,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1076])],[(0,[z1,z24,z3,z4,z1013,z5]),(0,[z1077,z1,z3,z4,z5,z8]),(1,[z1,z3,z709,z5,z8]),(0,[z109,z1,z2,z4,z890,z8])],[(0,[z1,z2,z687,z160,z5,z8]),(0,[z1,z2,z3,z4,z5,z1078])],[(0,[z17,z1,z218,z18,z3,z5]),(0,[z1,z1079,z3,z4,z5,z8])],[(0,[z1,z1080,z3,z4,z5,z8])],[(0,[z1,z2,z3,z377,z5,z361]),(0,[z1,z2,z3,z1081,z5,z8])],[(0,[z18,z3,z4,z5,z261,z8]),(0,[z1,z18,z3,z4,z5,z60]),(0,[z1,z2,z3,z767,z5,z8]),(0,[z1,z2,z1082,z4,z5,z8]),(0,[z1,z3,z1083,z4,z5,z8]),(0,[z1,z2,z3,z4,z448,z32]),(0,[z1,z3,z1084,z4,z5,z8]),(0,[z1,z2,z56,z57,z5,z12])],[(0,[z519,z18,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z771]),(0,[z1,z24,z393,z4,z5,z8]),(0,[z1,z150,z3,z159,z5,z8]),(0,[z1,z2,z4,z5,z555,z12])],[(0,[z1,z24,z3,z4,z5,z1021]),(0,[z1,z255,z3,z57,z5,z8])],[(0,[z1,z24,z446,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z225]),(0,[z1,z2,z3,z4,z5,z1085])],[(0,[z1,z18,z3,z4,z310,z8]),(0,[z1,z2,z3,z375,z5,z6]),(0,[z1,z2,z3,z4,z5,z1086]),(0,[z1,z2,z564,z4,z5,z12]),(0,[z1,z3,z4,z5,z8,z195]),(0,[z1,z2,z3,z4,z5,z1087]),(0,[z1,z2,z3,z4,z729,z8]),(0,[z1,z2,z3,z1088,z5,z8])],[(0,[z24,z157,z3,z4,z5,z8]),(0,[z1,z273,z3,z4,z7,z8]),(0,[z1,z2,z4,z567,z5,z12])],[(0,[z1,z121,z2,z3,z602,z5]),(0,[z1089,z1,z3,z4,z5,z8])],[(0,[z105,z1,z18,z814,z4,z5]),(0,[z1,z3,z4,z204,z729,z8])],[(0,[z289,z2,z157,z3,z4,z5]),(0,[z1,z2,z176,z4,z5,z131]),(0,[z1,z2,z3,z4,z5,z1090]),(0,[z1,z2,z1091,z4,z5,z8])]],
   [[(0,[z1,z24,z458,z4,z5,z8]),(0,[z1,z24,z3,z4,z5,z131]),(0,[z1,z2,z4,z1092,z5,z8]),(0,[z1,z255,z3,z4,z5,z316]),(0,[z110,z1093,z3,z4,z5,z8]),(0,[z1,z3,z4,z5,z12,z195])],[(0,[z1,z2,z3,z4,z1094,z8]),(0,[z76,z17,z1,z3,z5,z8]),(0,[z1,z1095,z3,z4,z5,z8])],[(0,[z1,z18,z3,z4,z5,z111]),(0,[z289,z2,z3,z4,z5,z252]),(0,[z1,z2,z173,z4,z5,z12])],[(0,[z1,z18,z3,z5,z8,z803]),(0,[z1,z2,z3,z5,z120,z8])],[(0,[z105,z1,z2,z814,z4,z5]),(0,[z1,z24,z3,z471,z5,z8]),(0,[z54,z1,z3,z709,z5,z8])],[(0,[z1,z3,z232,z4,z5,z8]),(0,[z1,z46,z3,z5,z126,z8]),(0,[z1,z3,z1096,z4,z5,z8]),(0,[z1,z2,z3,z1097,z5,z8])],[(0,[z1,z2,z3,z1098,z5,z8])],[(0,[z1,z18,z3,z4,z5,z8]),(0,[z1,z18,z129,z4,z5,z12]),(0,[z1,z2,z3,z4,z5,z1099]),(0,[z90,z2,z3,z602,z5,z70])],[(0,[z1,z2,z1100,z4,z5,z8]),(0,[z1,z2,z3,z4,z1101,z8]),(0,[z363,z2,z3,z4,z45,z8]),(0,[z1,z2,z245,z4,z7,z8]),(0,[z1,z2,z3,z4,z5,z1102]),(0,[z1,z2,z294,z4,z5,z425])],[(0,[z1,z18,z3,z787,z4,z5]),(0,[z1,z2,z3,z4,z1103,z5]),(0,[z90,z1,z2,z294,z4,z5]),(0,[z1,z2,z11,z239,z5,z12]),(0,[z1,z95,z2,z3,z5,z103]),(0,[z1,z2,z4,z428,z5,z103])],[(0,[z109,z1,z24,z4,z5,z12]),(0,[z1,z3,z4,z5,z8,z1104]),(0,[z1,z2,z3,z188,z5,z454]),(0,[z1,z2,z3,z4,z5,z1105]),(0,[z1,z2,z3,z4,z16,z168])],[(0,[z1,z18,z3,z4,z707,z5]),(0,[z1,z24,z3,z962,z5,z8]),(0,[z1,z2,z973,z3,z5,z8]),(0,[z1,z2,z3,z4,z5,z1106]),(0,[z1,z3,z1107,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1108]),(0,[z1,z2,z3,z1109,z5,z8]),(0,[z1,z2,z3,z4,z5,z316])],[(0,[z1,z162,z3,z4,z5,z8]),(0,[z1,z2,z196,z4,z5,z197]),(0,[z383,z2,z3,z106,z5,z8]),(0,[z1,z2,z458,z188,z5,z8]),(0,[z1,z2,z3,z4,z5,z1110]),(0,[z1,z2,z3,z5,z120,z25]),(0,[z1,z1111,z3,z4,z5,z8])],[(0,[z1,z24,z3,z4,z5,z293]),(0,[z1,z3,z176,z239,z5,z8])],[(0,[z1,z18,z3,z4,z5,z74]),(0,[z1,z2,z3,z4,z1112,z8]),(0,[z1,z3,z232,z4,z5,z25])],[(0,[z1,z2,z3,z4,z5,z1113]),(0,[z1,z2,z245,z4,z5,z70]),(0,[z1,z2,z3,z4,z5,z1114])]],
   [[(0,[z1,z18,z3,z4,z5,z25]),(0,[z1,z2,z3,z4,z5,z1115]),(0,[z167,z24,z3,z4,z5,z8]),(0,[z379,z2,z129,z4,z5,z8]),(0,[z1,z2,z236,z4,z5,z328]),(0,[z1,z1116,z3,z4,z5,z8]),(0,[z1,z2,z3,z1088,z5,z12])],[(0,[z1,z1117,z18,z3,z4,z5]),(0,[z17,z105,z1,z18,z3,z5]),(0,[z53,z2,z3,z106,z5,z328]),(0,[z1,z2,z10,z4,z5,z25])],[(0,[z1,z24,z3,z31,z4,z140]),(0,[z119,z219,z129,z4,z5,z8]),(0,[z1,z1118,z3,z4,z5,z8]),(0,[z1,z173,z10,z4,z5,z8])],[(0,[z1,z24,z56,z57,z5,z8]),(0,[z597,z2,z3,z4,z27,z8]),(0,[z1,z42,z11,z4,z5,z361]),(0,[z1,z2,z3,z1119,z5,z8])],[(0,[z1,z2,z3,z4,z5,z1120]),(0,[z1,z2,z3,z5,z1121,z8]),(0,[z1,z2,z3,z4,z5,z1122]),(0,[z1,z2,z4,z428,z5,z8])],[(0,[z1,z162,z3,z4,z5,z25]),(0,[z1,z2,z245,z602,z5,z8]),(0,[z1,z2,z3,z62,z5,z60])],[(0,[z17,z1,z24,z3,z5,z8]),(0,[z1,z2,z3,z1123,z5,z8]),(0,[z1,z2,z10,z4,z5,z374])],[(0,[z1,z2,z3,z4,z5,z1124]),(0,[z54,z1,z254,z3,z5,z8]),(0,[z1,z2,z236,z4,z5,z1125])],[(0,[z610,z1,z176,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1126]),(0,[z1,z2,z3,z5,z120,z12]),(0,[z39,z805,z3,z4,z5,z8])],[(0,[z105,z1,z3,z4,z5,z217])],[(0,[z18,z3,z4,z5,z8,z523]),(0,[z105,z1,z3,z43,z4,z5]),(0,[z1,z2,z3,z4,z1127,z8]),(0,[z1,z1128,z3,z4,z5,z8]),(0,[z1,z3,z232,z4,z5,z12]),(0,[z14,z1,z2,z3,z5,z103])],[(0,[z39,z2,z3,z4,z5,z8]),(0,[z515,z2,z3,z4,z5,z70]),(0,[z1,z2,z147,z4,z5,z12])],[(0,[z1,z18,z3,z4,z5,z12]),(0,[z1,z18,z3,z4,z5,z214]),(0,[z1,z2,z129,z4,z5,z1051]),(0,[z1,z254,z196,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z47]),(0,[z1,z2,z4,z428,z5,z25])],[(0,[z1,z2,z3,z4,z5,z1129]),(0,[z1,z42,z3,z239,z5,z8])],[(0,[z1,z24,z3,z4,z296,z5]),(0,[z1,z2,z549,z4,z5,z12]),(0,[z1,z3,z4,z5,z8,z1130])]],
   [[(0,[z1,z2,z3,z4,z5,z1131]),(0,[z1,z2,z1132,z3,z5,z8]),(0,[z1,z2,z1133,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1134])],[(0,[z1,z18,z3,z410,z5,z8]),(0,[z1,z24,z3,z4,z5,z990]),(0,[z948,z1,z2,z3,z5,z8]),(0,[z1,z2,z3,z5,z1135,z8])],[],[(0,[z1,z2,z716,z4,z5,z8]),(0,[z1,z2,z687,z4,z5,z12]),(0,[z1,z2,z3,z4,z1127,z25]),(0,[z1,z1136,z3,z4,z5,z8]),(0,[z1,z2,z3,z5,z182,z741])],[(1,[z1,z2,z787,z4,z5]),(0,[z1,z2,z3,z4,z1137,z8]),(0,[z83,z1,z3,z4,z5,z8]),(0,[z39,z2,z3,z4,z5,z25])],[(0,[z1,z3,z1138,z4,z5,z8]),(0,[z1,z2,z1139,z4,z5,z8]),(0,[z39,z173,z3,z4,z5,z8]),(0,[z659,z1,z2,z4,z5,z12]),(0,[z1,z2,z3,z5,z286,z103])],[(0,[z18,z3,z4,z5,z8,z545]),(0,[z1,z2,z10,z4,z5,z843])],[(0,[z461,z1,z2,z4,z5,z12]),(0,[z1,z2,z1140,z4,z5,z8]),(0,[z1,z2,z4,z717,z5,z8]),(0,[z1,z2,z1141,z4,z5,z8])],[(0,[z1,z18,z3,z4,z5,z29]),(0,[z1,z2,z185,z4,z5,z12]),(0,[z1,z2,z236,z36,z5,z8]),(0,[z69,z238,z3,z4,z27,z8])],[(0,[z1,z2,z1142,z4,z5,z8]),(1,[z2,z26,z4,z308,z8]),(0,[z53,z2,z3,z855,z5,z8]),(0,[z1,z2,z3,z4,z5,z1143]),(0,[z607,z2,z3,z36,z5,z8]),(0,[z69,z414,z3,z4,z27,z8]),(0,[z1,z2,z10,z4,z5,z29]),(0,[z39,z2,z3,z4,z5,z325]),(0,[z39,z2,z3,z4,z5,z374]),(0,[z1,z2,z4,z428,z5,z12])],[(0,[z1,z297,z3,z4,z5,z8]),(0,[z1,z2,z446,z471,z5,z8]),(0,[z2,z3,z4,z27,z966,z8]),(0,[z1,z2,z1144,z4,z5,z8]),(0,[z1,z2,z4,z5,z25,z652]),(0,[z1,z2,z4,z769,z5,z8]),(0,[z1,z2,z3,z102,z5,z528])],[(0,[z1,z332,z201,z4,z5,z8]),(0,[z1,z24,z3,z4,z5,z225]),(0,[z1,z2,z3,z5,z8,z829]),(0,[z1,z2,z3,z4,z1145,z12])],[(0,[z249,z2,z3,z36,z5,z8]),(0,[z1,z2,z3,z4,z5,z1146]),(0,[z1,z2,z3,z213,z4,z140])],[(0,[z1,z18,z3,z4,z308,z8]),(0,[z1,z24,z3,z91,z5,z8]),(0,[z1,z121,z3,z4,z5,z22]),(0,[z83,z1,z3,z4,z5,z25])],[(0,[z105,z1,z3,z4,z5,z137]),(0,[z1,z2,z660,z4,z5,z12]),(0,[z1,z2,z3,z471,z5,z454])],[(0,[z1,z2,z3,z1147,z5,z8]),(0,[z1,z2,z3,z4,z5,z1148]),(0,[z1,z3,z709,z179,z5,z8]),(0,[z54,z1,z3,z287,z5,z8]),(0,[z72,z1,z3,z4,z5,z903]),(0,[z1,z1149,z3,z4,z5,z8])]],
   [[(0,[z1,z2,z458,z471,z5,z8]),(0,[z39,z2,z3,z4,z5,z12])],[(0,[z187,z18,z3,z36,z5,z8]),(0,[z1,z2,z3,z4,z5,z1150]),(0,[z1,z2,z3,z4,z5,z1051]),(0,[z1,z716,z176,z4,z5,z8]),(0,[z1,z2,z3,z141,z5,z8])],[(0,[z483,z17,z1,z3,z5,z8]),(0,[z268,z18,z3,z4,z5,z8]),(0,[z1,z218,z75,z3,z4,z5]),(0,[z277,z1,z2,z4,z5,z12]),(0,[z110,z2,z4,z5,z142,z8])],[(0,[z1,z2,z196,z4,z310,z8]),(0,[z1,z297,z3,z4,z5,z25]),(0,[z1,z2,z3,z678,z28,z8]),(0,[z1,z2,z3,z4,z5,z1151]),(0,[z90,z167,z2,z3,z4,z5]),(0,[z1,z2,z4,z5,z834,z12])],[(0,[z1,z2,z1152,z4,z5,z8]),(0,[z1,z24,z3,z5,z120,z8]),(0,[z1,z2,z4,z27,z81,z12]),(0,[z1,z121,z3,z5,z22,z23]),(0,[z1,z2,z3,z102,z5,z741])],[(0,[z17,z105,z1,z3,z4,z5]),(0,[z257,z2,z3,z4,z5,z252]),(0,[z54,z1,z3,z417,z5,z8]),(0,[z39,z2,z3,z410,z5,z8])],[(0,[z1,z161,z3,z4,z5,z8]),(0,[z1,z2,z3,z159,z5,z8]),(0,[z1,z2,z247,z4,z5,z12]),(0,[z1,z2,z3,z1153,z5,z8]),(0,[z1,z2,z3,z4,z5,z1154]),(0,[z1155,z1,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z1156,z8]),(0,[z1,z3,z4,z5,z1157,z8]),(0,[z1,z2,z3,z4,z5,z1158]),(0,[z1,z2,z3,z501,z5,z103]),(0,[z1,z2,z3,z5,z741,z103])],[(0,[z1,z161,z3,z4,z5,z221]),(0,[z1,z2,z3,z4,z5,z1159]),(0,[z1,z2,z3,z4,z1160,z5]),(0,[z1,z46,z3,z43,z5,z47]),(0,[z659,z1,z2,z160,z5,z8]),(0,[z1,z2,z3,z495,z28,z8])],[(0,[z1,z68,z3,z499,z5,z8]),(0,[z1,z24,z1100,z4,z5,z8]),(0,[z1,z24,z11,z4,z5,z12]),(0,[z1,z2,z1161,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1162]),(0,[z83,z1,z3,z4,z5,z12])],[(0,[z1,z2,z688,z4,z5,z12]),(0,[z1,z18,z3,z5,z304,z8]),(0,[z54,z1,z2,z3,z34,z8]),(0,[z1,z2,z177,z4,z5,z8]),(0,[z1,z2,z3,z141,z5,z25])],[(0,[z64,z1163,z3,z4,z5,z8]),(0,[z389,z1,z3,z235,z5,z8]),(0,[z1,z2,z3,z4,z5,z1164]),(0,[z1,z2,z1165,z4,z5,z8])],[(0,[z1,z2,z201,z4,z5,z12]),(0,[z1,z24,z3,z4,z5,z316]),(0,[z995,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1166])],[(0,[z1,z2,z3,z4,z5,z1167]),(0,[z1,z2,z1168,z4,z5,z8]),(0,[z90,z2,z3,z4,z7,z70]),(0,[z1,z2,z3,z4,z155,z32]),(0,[z54,z1,z2,z3,z5,z47])],[(0,[z1,z2,z1169,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1170]),(0,[z1,z2,z3,z4,z5,z1171]),(0,[z703,z2,z3,z4,z27,z8]),(0,[z1,z2,z3,z377,z5,z8])],[(0,[z1,z18,z3,z4,z5,z314]),(0,[z1,z2,z196,z4,z5,z8]),(0,[z1,z2,z3,z159,z5,z25]),(0,[z1,z297,z3,z4,z5,z12]),(0,[z1,z161,z3,z4,z5,z25]),(0,[z1,z2,z3,z4,z298,z70]),(0,[z1,z121,z75,z3,z4,z5]),(0,[z1,z2,z4,z428,z5,z252]),(0,[z1155,z1,z3,z4,z5,z25]),(0,[z1,z2,z3,z102,z5,z182])]],
   [[(0,[z1,z2,z3,z4,z5,z1172]),(1,[z1,z2,z4,z5,z843]),(0,[z1,z2,z3,z4,z1173,z8])],[(0,[z1,z2,z3,z4,z5,z780]),(0,[z1,z24,z3,z4,z5,z454]),(0,[z1,z2,z3,z1174,z5,z8]),(0,[z1,z203,z3,z4,z204,z8]),(0,[z1,z2,z3,z1175,z5,z8]),(0,[z1,z2,z3,z4,z5,z741])],[(0,[z1,z24,z10,z4,z5,z25]),(0,[z1,z88,z3,z4,z34,z8]),(0,[z72,z1,z2,z4,z428,z5]),(0,[z1,z3,z4,z5,z8,z1176]),(0,[z1,z2,z3,z5,z1177,z8])],[(0,[z670,z18,z3,z4,z5,z8]),(0,[z1,z2,z1178,z4,z5,z8]),(0,[z1,z2,z177,z4,z5,z25]),(0,[z1,z2,z3,z4,z5,z1179]),(0,[z83,z1,z3,z4,z140,z5])],[(0,[z1,z18,z3,z188,z5,z8]),(0,[z606,z1,z2,z3,z5,z103]),(0,[z1,z2,z3,z4,z5,z1180])],[(0,[z1,z2,z1181,z4,z5,z8]),(0,[z1,z18,z3,z4,z5,z901]),(0,[z1,z219,z3,z4,z5,z8]),(0,[z1,z24,z4,z428,z5,z8]),(0,[z1,z2,z3,z602,z298,z8]),(0,[z116,z1,z2,z4,z5,z12]),(0,[z1,z2,z4,z5,z29,z12])],[(0,[z1,z2,z3,z106,z34,z8]),(0,[z1,z2,z3,z141,z5,z12]),(0,[z1,z110,z2,z4,z5,z12]),(0,[z1,z2,z4,z145,z81,z12]),(0,[z1182,z1,z3,z4,z5,z8])],[(0,[z109,z1,z18,z4,z142,z8]),(0,[z1,z46,z254,z3,z5,z8]),(0,[z1,z2,z3,z1183,z5,z8]),(0,[z1,z2,z3,z377,z5,z25]),(0,[z1,z3,z4,z5,z12,z1176])],[(0,[z1,z18,z3,z5,z807,z8]),(0,[z191,z1,z18,z160,z5,z8]),(0,[z1,z2,z196,z4,z5,z25]),(0,[z508,z1,z3,z4,z5,z137])],[(0,[z105,z1,z18,z3,z4,z5]),(0,[z1,z205,z3,z159,z5,z8])],[(0,[z1,z3,z716,z4,z5,z8]),(0,[z1,z203,z3,z4,z204,z25]),(0,[z1,z2,z4,z331,z5,z25])],[(0,[z1,z1184,z3,z4,z5,z8]),(0,[z1,z18,z3,z239,z5,z8]),(0,[z1,z24,z3,z4,z34,z8]),(0,[z1,z2,z3,z159,z5,z12]),(0,[z1,z2,z3,z4,z5,z1185]),(0,[z1,z161,z3,z4,z5,z12]),(0,[z1,z203,z3,z4,z729,z8]),(0,[z1,z2,z57,z769,z5,z8])],[(0,[z1,z2,z3,z4,z5,z1186]),(0,[z1,z18,z3,z4,z5,z221]),(0,[z39,z24,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1187])],[(0,[z24,z18,z3,z4,z5,z8]),(0,[z1,z18,z294,z4,z5,z8]),(0,[z1,z2,z3,z1188,z5,z8]),(0,[z1,z3,z4,z5,z8,z903]),(0,[z109,z1,z2,z4,z142,z8])],[(0,[z1,z24,z3,z4,z5,z47]),(0,[z1,z219,z3,z4,z5,z25]),(0,[z191,z1,z2,z160,z5,z8]),(0,[z1,z56,z232,z57,z5,z8])],[(0,[z105,z1,z2,z3,z4,z5]),(0,[z1,z2,z393,z4,z5,z225]),(0,[z363,z2,z3,z4,z5,z70]),(0,[z1,z2,z177,z4,z5,z12]),(0,[z72,z1,z2,z3,z5,z23]),(0,[z1,z48,z3,z473,z5,z8]),(0,[z1,z2,z4,z5,z8,z843])]],
   [[(0,[z1,z2,z3,z1189,z5,z8]),(0,[z1,z2,z11,z4,z5,z131]),(0,[z1,z173,z4,z5,z8,z12])],[(0,[z1,z2,z3,z899,z5,z8]),(0,[z1,z2,z3,z1190,z5,z8]),(0,[z1,z2,z393,z91,z5,z8])],[(0,[z1,z2,z3,z4,z16,z32])],[(0,[z1,z93,z3,z4,z127,z8]),(0,[z229,z18,z3,z4,z5,z8]),(0,[z1,z2,z3,z377,z5,z12])],[(0,[z1,z2,z3,z4,z385,z52]),(0,[z1,z2,z196,z4,z5,z12]),(0,[z187,z297,z3,z36,z5,z8]),(0,[z1,z2,z3,z1191,z5,z8]),(0,[z1,z2,z97,z4,z5,z12]),(0,[z1,z2,z33,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z1192]),(0,[z90,z2,z3,z4,z5,z70]),(0,[z1,z2,z3,z4,z1173,z12])],[(0,[z24,z18,z3,z4,z5,z25]),(0,[z1,z2,z999,z3,z5,z8]),(0,[z2,z3,z4,z5,z8,z747]),(0,[z1,z203,z3,z4,z204,z12]),(0,[z109,z1,z2,z4,z142,z25])],[(0,[z1,z273,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1193]),(0,[z0,z2,z26,z4,z5,z52]),(0,[z54,z1,z3,z504,z5,z8]),(0,[z191,z1,z2,z160,z5,z25]),(0,[z1,z2,z3,z5,z1177,z12])],[(0,[z1,z1194,z3,z4,z5,z8]),(0,[z1,z1195,z3,z4,z5,z8]),(0,[z1,z18,z3,z4,z5,z325]),(0,[z1,z18,z3,z4,z5,z374]),(0,[z1,z238,z3,z4,z5,z8]),(1,[z2,z446,z4,z45,z8])],[(0,[z1,z2,z3,z4,z5,z1196]),(0,[z1,z18,z3,z375,z5,z8]),(0,[z18,z3,z4,z512,z5,z8]),(0,[z1,z176,z4,z5,z123,z12]),(0,[z1,z2,z3,z4,z1145,z8])],[(0,[z64,z105,z18,z3,z4,z5]),(0,[z1,z219,z3,z4,z5,z12]),(0,[z1,z2,z1197,z4,z5,z8]),(0,[z53,z132,z2,z3,z5,z8]),(0,[z72,z1,z2,z245,z4,z5]),(0,[z641,z2,z3,z4,z5,z252])],[(0,[z1,z2,z3,z4,z5,z1198]),(0,[z1,z2,z177,z4,z5,z29]),(0,[z109,z1,z2,z4,z142,z325]),(0,[z109,z1,z2,z4,z142,z374])],[(0,[z17,z1,z42,z3,z5,z8]),(0,[z1,z2,z3,z159,z308,z8]),(0,[z119,z2,z419,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1199]),(0,[z130,z1,z176,z4,z5,z9]),(0,[z1200,z1,z3,z4,z5,z8])],[(0,[z1,z2,z814,z4,z5,z8]),(0,[z1,z294,z43,z4,z5,z8]),(0,[z1,z2,z33,z4,z5,z25])],[(0,[z941,z1,z2,z3,z4,z5]),(0,[z1,z1201,z3,z4,z5,z8])],[(0,[z2,z1163,z3,z4,z5,z8]),(0,[z1,z254,z3,z4,z5,z328]),(0,[z1,z2,z3,z377,z5,z29]),(0,[z1,z2,z3,z241,z28,z8])]],
   [[(0,[z1,z273,z3,z4,z5,z25]),(0,[z1202,z2,z3,z4,z5,z8]),(0,[z110,z2,z3,z4,z81,z8])],[(1,[z1,z18,z787,z4,z5]),(0,[z1,z238,z3,z4,z5,z25]),(0,[z1,z162,z393,z4,z5,z8]),(0,[z337,z1,z2,z4,z5,z12]),(0,[z1,z2,z3,z663,z4,z140])],[(0,[z24,z18,z3,z4,z5,z12]),(0,[z1203,z1,z2,z3,z5,z8]),(0,[z1,z24,z3,z141,z5,z8]),(0,[z107,z2,z26,z4,z5,z8]),(0,[z1,z2,z33,z4,z5,z374]),(0,[z109,z1,z2,z4,z142,z12])],[(0,[z1,z2,z245,z4,z5,z8]),(0,[z191,z1,z2,z160,z5,z12]),(0,[z110,z1204,z3,z4,z5,z8]),(0,[z1,z1205,z3,z4,z5,z8])],[(0,[z95,z18,z3,z4,z5,z8]),(0,[z69,z2,z3,z4,z966,z8]),(0,[z54,z1,z3,z5,z8,z195]),(0,[z1,z2,z3,z4,z5,z1206])],[(0,[z1,z2,z3,z1207,z5,z8]),(0,[z1,z1208,z3,z4,z5,z8]),(0,[z1,z2,z3,z1209,z5,z8])],[(0,[z1,z2,z4,z296,z717,z5]),(0,[z110,z48,z3,z4,z5,z8])],[(0,[z1,z24,z3,z159,z5,z8]),(0,[z1,z88,z196,z4,z5,z8]),(0,[z1,z2,z446,z4,z5,z454]),(0,[z1,z2,z544,z4,z5,z12]),(0,[z1,z2,z3,z4,z5,z1210]),(0,[z109,z1,z2,z410,z142,z8])],[(0,[z1,z2,z3,z4,z5,z265])],[(0,[z1,z2,z189,z4,z5,z12]),(0,[z1,z2,z3,z4,z5,z1211]),(0,[z1,z2,z33,z4,z5,z12]),(0,[z1,z2,z3,z869,z28,z8])],[(0,[z1,z2,z196,z4,z5,z861]),(0,[z1,z46,z2,z3,z34,z8]),(0,[z1,z2,z3,z1212,z5,z8]),(0,[z1213,z2,z3,z4,z5,z8])],[(0,[z1,z18,z3,z952,z4,z5]),(0,[z1,z24,z177,z4,z5,z8]),(0,[z1,z1214,z3,z4,z5,z8])],[(0,[z1,z1215,z3,z4,z5,z8]),(0,[z1,z273,z3,z4,z5,z12]),(0,[z1,z2,z245,z4,z5,z25]),(0,[z1,z2,z3,z15,z5,z8]),(0,[z1,z2,z1216,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z52]),(0,[z1,z1217,z3,z4,z5,z8]),(0,[z1,z2,z458,z4,z5,z454]),(0,[z1,z238,z3,z4,z5,z12]),(0,[z1,z46,z2,z3,z5,z47])],[(0,[z1,z1218,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z742,z16]),(0,[z1,z2,z3,z4,z140,z742]),(0,[z1,z1219,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z837]),(0,[z1,z2,z787,z4,z5,z8]),(0,[z412,z2,z3,z4,z45,z8]),(0,[z1220,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z682,z28,z8]),(1,[z1,z2,z3,z4,z742])]],
   [[(0,[z1,z24,z196,z4,z5,z8]),(0,[z1,z2,z1221,z4,z5,z8])],[(0,[z17,z24,z18,z3,z5,z8]),(0,[z1222,z1,z2,z4,z5,z8]),(0,[z1,z2,z3,z4,z1223,z8]),(0,[z1,z2,z11,z4,z5,z913]),(0,[z1,z2,z4,z428,z35,z5])],[(0,[z1,z150,z3,z4,z5,z52]),(0,[z1,z2,z3,z4,z1224,z8]),(0,[z1,z2,z3,z102,z5,z583]),(0,[z72,z1,z273,z3,z4,z5])],[(0,[z1,z161,z3,z188,z5,z8]),(1,[z2,z3,z4,z5,z747]),(0,[z1,z2,z3,z5,z8,z23])],[(0,[z18,z3,z564,z4,z5,z8]),(0,[z130,z1,z176,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1225])],[(0,[z1,z2,z113,z4,z5,z12]),(0,[z1,z2,z4,z81,z45,z12]),(0,[z1,z2,z3,z15,z5,z25]),(0,[z1,z3,z4,z764,z5,z126]),(0,[z1,z1226,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z310,z328]),(0,[z1,z2,z3,z4,z5,z1227]),(0,[z1,z1228,z3,z4,z5,z8])],[(0,[z64,z68,z18,z3,z5,z8]),(0,[z18,z3,z4,z5,z571,z8]),(0,[z1,z176,z4,z5,z216,z12]),(0,[z1,z46,z3,z709,z5,z8]),(0,[z1,z3,z43,z4,z296,z5]),(0,[z194,z1,z2,z3,z5,z741])],[(0,[z1,z18,z4,z5,z25,z12]),(0,[z1,z2,z245,z4,z5,z12]),(0,[z1,z2,z3,z1229,z4,z8]),(0,[z1,z2,z3,z5,z28,z60])],[(0,[z209,z1,z18,z4,z5,z12]),(0,[z1,z2,z3,z4,z5,z1230]),(0,[z1,z1231,z3,z4,z5,z8])],[(0,[z105,z1,z218,z3,z4,z5])],[(0,[z1,z1163,z3,z4,z5,z8]),(0,[z640,z18,z3,z4,z5,z8]),(0,[z1,z2,z458,z4,z5,z1129]),(0,[z1,z1232,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z1224,z25]),(0,[z1,z1149,z3,z4,z5,z25])],[(0,[z1,z2,z3,z4,z1233,z8])],[(0,[z130,z1,z176,z4,z5,z25]),(0,[z1,z1234,z3,z4,z5,z8])],[(0,[z1,z2,z260,z4,z5,z12]),(0,[z1,z2,z3,z4,z5,z1235]),(0,[z1,z2,z236,z4,z5,z1236]),(0,[z1,z2,z3,z1237,z5,z8]),(0,[z1238,z2,z3,z4,z5,z8])],[(0,[z1,z1239,z3,z4,z5,z8]),(0,[z54,z1,z3,z432,z5,z8]),(0,[z1,z2,z1240,z4,z5,z8]),(0,[z209,z1,z2,z4,z5,z12])]],
   [[(0,[z1,z205,z3,z4,z5,z52]),(0,[z1,z2,z3,z4,z5,z1241]),(0,[z1,z2,z3,z4,z5,z1242])],[(0,[z1,z18,z3,z4,z5,z6]),(0,[z1,z2,z1243,z4,z5,z8]),(0,[z1,z2,z789,z4,z5,z8]),(0,[z1,z2,z3,z15,z5,z12]),(0,[z1,z2,z3,z1229,z4,z25])],[(0,[z17,z1,z3,z5,z22,z8]),(0,[z1,z3,z1244,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z328]),(0,[z110,z173,z3,z4,z5,z8]),(0,[z1,z1217,z3,z4,z5,z12])],[(0,[z1,z2,z3,z4,z1245,z8]),(0,[z1,z24,z3,z4,z16,z32]),(0,[z1,z1246,z3,z4,z5,z8]),(0,[z1,z2,z3,z1247,z5,z8])],[(0,[z1,z2,z3,z5,z304,z32]),(0,[z1,z2,z3,z1248,z5,z8])],[(0,[z582,z18,z3,z4,z5,z8]),(0,[z1,z18,z3,z253,z5,z8]),(0,[z1,z2,z1117,z3,z4,z5]),(0,[z72,z1,z177,z4,z5,z137]),(0,[z1,z2,z4,z5,z25,z701])],[(0,[z64,z218,z18,z3,z4,z5]),(0,[z1,z2,z3,z602,z7,z8]),(0,[z1,z2,z3,z456,z5,z103]),(0,[z191,z1,z2,z160,z5,z314])],[(0,[z1,z584,z176,z4,z5,z8])],[(0,[z1,z68,z3,z43,z5,z8]),(0,[z1,z2,z3,z874,z5,z8]),(0,[z109,z1,z24,z4,z142,z8]),(0,[z209,z1,z2,z4,z5,z843])],[(0,[z191,z1,z24,z160,z5,z8]),(0,[z1,z1249,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1125]),(0,[z130,z1,z176,z4,z5,z12]),(0,[z54,z1,z294,z4,z5,z8]),(0,[z1,z2,z3,z4,z1250,z8])],[(0,[z105,z1,z24,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z980]),(0,[z1,z2,z3,z4,z1251,z8]),(0,[z1,z2,z598,z4,z81,z8])],[(0,[z1,z2,z3,z4,z869,z8])],[(0,[z1,z2,z3,z4,z5,z1252]),(0,[z1,z2,z3,z1253,z5,z8]),(0,[z1,z3,z43,z5,z120,z8]),(0,[z1,z2,z3,z4,z5,z1254]),(0,[z1,z2,z3,z1247,z5,z25])],[(0,[z1163,z18,z3,z4,z5,z8]),(0,[z1,z161,z446,z4,z5,z8]),(0,[z1,z2,z3,z602,z5,z70]),(0,[z1,z2,z4,z5,z25,z41]),(0,[z110,z2,z3,z4,z5,z12])],[(0,[z1,z2,z1255,z4,z5,z8]),(0,[z1,z2,z245,z4,z5,z252]),(0,[z1,z2,z4,z5,z890,z8])],[(0,[z1,z18,z176,z4,z5,z12]),(0,[z53,z2,z236,z106,z5,z8]),(0,[z1,z2,z419,z4,z5,z12]),(0,[z1,z2,z3,z1256,z5,z8]),(0,[z1,z2,z757,z4,z5,z8])]],
   [[(0,[z1,z2,z10,z4,z5,z225]),(0,[z1,z1257,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z966,z8]),(0,[z1,z2,z3,z4,z5,z1258])],[(0,[z37,z288,z3,z4,z45,z8]),(0,[z1,z2,z294,z4,z5,z182]),(1,[z1,z2,z3,z5,z741])],[(0,[z1,z2,z3,z4,z298,z8])],[(0,[z1,z24,z245,z4,z5,z8]),(0,[z1,z2,z638,z4,z5,z12]),(0,[z1,z46,z3,z5,z8,z195])],[(0,[z1,z1259,z3,z4,z5,z8]),(0,[z1,z18,z3,z1008,z5,z8]),(0,[z1,z2,z3,z4,z5,z1260]),(0,[z1,z3,z4,z5,z8,z1261]),(0,[z1,z2,z3,z445,z4,z465])],[(0,[z107,z1,z2,z4,z5,z12]),(0,[z1,z162,z3,z91,z5,z8]),(0,[z1,z2,z3,z1262,z5,z8])],[(0,[z1,z3,z4,z5,z1263,z8]),(0,[z119,z2,z129,z4,z5,z513]),(0,[z1,z2,z1264,z4,z5,z8]),(0,[z1,z161,z3,z471,z5,z8]),(0,[z1,z2,z649,z4,z5,z12]),(0,[z1,z2,z294,z4,z5,z32]),(0,[z1,z121,z3,z4,z5,z174]),(0,[z1,z2,z3,z4,z25,z824])],[(0,[z285,z2,z3,z36,z5,z8])],[(0,[z1,z2,z3,z1265,z5,z8]),(0,[z1266,z2,z3,z4,z5,z8])],[(0,[z1,z344,z3,z4,z396,z8]),(0,[z1,z254,z236,z4,z5,z8]),(0,[z1,z1267,z3,z4,z5,z8]),(0,[z1,z3,z4,z5,z12,z1261])],[(0,[z1268,z1,z18,z3,z4,z5]),(0,[z53,z254,z3,z106,z5,z8])],[(0,[z1,z414,z3,z4,z5,z8]),(0,[z481,z1,z176,z4,z5,z8]),(0,[z1,z1269,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z298,z25]),(0,[z1,z46,z3,z381,z5,z8]),(0,[z109,z1,z173,z4,z5,z12]),(0,[z1270,z2,z3,z4,z5,z8])],[(0,[z1,z18,z11,z4,z5,z12]),(0,[z1,z2,z26,z4,z5,z74]),(0,[z1,z2,z3,z4,z35,z168])],[(0,[z1,z18,z4,z5,z1019,z8]),(0,[z1,z42,z11,z4,z5,z8])],[(0,[z1,z18,z393,z4,z5,z8]),(0,[z18,z3,z189,z4,z5,z8]),(0,[z1203,z1,z18,z3,z5,z8]),(0,[z1,z1132,z75,z3,z5,z8]),(0,[z1,z2,z3,z4,z1271,z8]),(0,[z1,z2,z31,z4,z428,z5])]],
   [[(0,[z1,z2,z3,z4,z5,z1272])],[(0,[z1,z18,z446,z4,z5,z8]),(0,[z1268,z1,z2,z3,z4,z5]),(0,[z292,z1,z3,z4,z123,z8])],[(0,[z54,z1,z68,z3,z5,z8]),(0,[z336,z2,z3,z4,z45,z8]),(0,[z1,z2,z21,z4,z5,z12])],[(0,[z17,z1,z254,z3,z5,z8]),(0,[z1,z2,z3,z4,z5,z1273]),(0,[z1,z2,z3,z1274,z5,z8]),(0,[z1275,z1,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z361]),(0,[z1,z2,z3,z4,z5,z1276]),(0,[z1,z2,z3,z473,z5,z8])],[(0,[z1,z18,z3,z4,z5,z454]),(0,[z483,z1,z3,z4,z366,z8]),(0,[z1,z414,z3,z4,z5,z25])],[(0,[z1,z2,z3,z4,z5,z1277]),(0,[z119,z2,z789,z4,z5,z8]),(0,[z1,z1278,z3,z4,z5,z8]),(0,[z1,z1279,z3,z4,z5,z8])],[(0,[z1,z18,z458,z4,z5,z8]),(0,[z1,z18,z3,z4,z5,z131]),(0,[z1,z2,z3,z4,z5,z1280]),(0,[z1281,z2,z3,z4,z5,z8]),(0,[z1,z42,z11,z4,z5,z25]),(0,[z54,z72,z1,z3,z5,z103])],[(0,[z1,z2,z3,z4,z298,z12])],[(0,[z124,z24,z3,z4,z5,z8]),(0,[z1,z2,z3,z1282,z5,z8]),(0,[z109,z39,z2,z4,z5,z12])],[(0,[z1,z1283,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z1284]),(0,[z1,z18,z3,z471,z5,z8]),(0,[z1,z2,z3,z4,z1285,z8]),(0,[z439,z24,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z491]),(0,[z1,z121,z3,z253,z5,z22])],[(0,[z18,z3,z241,z4,z5,z8]),(0,[z1,z273,z393,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1286]),(0,[z1,z2,z3,z4,z1287,z8]),(0,[z1,z2,z3,z140,z5,z304]),(0,[z1,z2,z31,z4,z140,z428])],[(0,[z1,z2,z3,z4,z5,z1236]),(0,[z2,z3,z855,z106,z5,z8]),(0,[z1,z2,z3,z141,z296,z5]),(0,[z1,z967,z3,z4,z5,z8]),(0,[z1,z2,z3,z473,z5,z25])],[(0,[z1222,z1,z18,z4,z5,z8]),(0,[z1,z173,z3,z473,z5,z8]),(0,[z1288,z2,z3,z4,z5,z8])],[(0,[z1,z3,z4,z5,z8,z1289]),(0,[z1,z2,z1042,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1290]),(0,[z1,z2,z4,z1291,z5,z8]),(0,[z1,z2,z1292,z4,z5,z8])]],
   [[(0,[z1,z2,z3,z937,z4,z5]),(0,[z1,z2,z3,z159,z5,z6]),(0,[z1,z2,z3,z4,z5,z1293]),(0,[z1,z2,z3,z5,z120,z293]),(0,[z1,z2,z3,z4,z1294,z8])],[(0,[z1,z18,z3,z4,z1041,z5]),(0,[z1,z414,z3,z4,z5,z12])],[(0,[z1,z24,z3,z377,z5,z8]),(0,[z1,z2,z3,z473,z5,z325]),(0,[z1,z2,z3,z473,z5,z374])],[(0,[z105,z1,z2,z68,z3,z5]),(0,[z1,z24,z3,z102,z5,z182]),(0,[z1,z1295,z3,z4,z5,z8]),(0,[z1,z2,z3,z1296,z5,z8]),(0,[z1,z3,z4,z5,z8,z1297]),(0,[z1,z42,z11,z4,z5,z12])],[(0,[z1,z18,z3,z4,z5,z293]),(0,[z1,z2,z3,z1298,z5,z8]),(0,[z1,z2,z1299,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1300])],[(0,[z1,z2,z3,z4,z5,z1301]),(0,[z1,z2,z3,z4,z5,z1302]),(0,[z1,z2,z294,z4,z5,z137])],[(0,[z1,z18,z3,z4,z1048,z5]),(0,[z1,z2,z4,z465,z81,z12])],[(0,[z1,z68,z18,z3,z5,z8]),(0,[z1,z1093,z3,z4,z5,z8]),(0,[z1,z1303,z3,z4,z5,z8])],[(0,[z1,z2,z3,z946,z4,z5]),(0,[z1,z2,z3,z4,z1304,z8]),(0,[z1,z2,z3,z4,z5,z1305]),(0,[z1,z2,z3,z4,z5,z1306])],[(0,[z1,z18,z3,z31,z4,z140]),(0,[z1,z1307,z3,z4,z5,z8]),(0,[z1,z2,z3,z1308,z5,z8]),(0,[z1,z2,z3,z473,z5,z12]),(0,[z1,z2,z1309,z4,z5,z8])],[(0,[z1,z18,z56,z57,z5,z8]),(0,[z209,z1,z24,z4,z5,z12]),(0,[z1,z2,z3,z4,z5,z1310]),(0,[z1,z3,z303,z43,z5,z8]),(0,[z1,z2,z581,z4,z5,z12]),(0,[z1,z2,z3,z5,z8,z1311]),(0,[z1,z1312,z3,z4,z5,z8])],[(0,[z1,z2,z218,z3,z4,z5]),(0,[z110,z2,z3,z4,z5,z8]),(0,[z605,z1,z2,z4,z5,z12]),(0,[z1,z2,z1313,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1314]),(0,[z1,z2,z3,z5,z12,z23]),(0,[z194,z1,z3,z5,z195,z103]),(0,[z1,z1315,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z1025]),(0,[z69,z2,z3,z4,z27,z8]),(0,[z1,z2,z3,z4,z5,z772])],[(0,[z1,z1316,z3,z4,z5,z8]),(0,[z0,z2,z26,z4,z385,z8]),(0,[z1,z2,z236,z4,z5,z8]),(0,[z1,z1317,z3,z4,z5,z8]),(0,[z1,z2,z1318,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1319])],[(0,[z1,z2,z3,z4,z5,z1320]),(0,[z1,z469,z3,z4,z5,z272]),(0,[z53,z2,z3,z106,z5,z8]),(0,[z1,z2,z3,z4,z298,z252]),(0,[z1,z3,z4,z5,z22,z47]),(0,[z1,z2,z56,z57,z5,z316]),(0,[z1,z2,z3,z1321,z5,z8])],[(0,[z1,z3,z1322,z4,z5,z8]),(0,[z1,z2,z3,z375,z5,z52]),(0,[z250,z1,z2,z160,z5,z8]),(0,[z1,z1323,z3,z4,z5,z8]),(0,[z72,z1,z2,z3,z602,z5]),(0,[z1,z42,z11,z4,z5,z29]),(0,[z1,z2,z3,z1324,z5,z8]),(0,[z1,z2,z4,z81,z5,z74]),(0,[z1,z2,z3,z5,z12,z1311])]],
   [[(0,[z1,z68,z18,z3,z5,z25]),(0,[z1,z2,z3,z4,z5,z1325]),(0,[z1,z3,z4,z5,z1326,z8]),(0,[z1,z1327,z3,z4,z5,z8])],[(0,[z0,z2,z789,z4,z5,z8]),(0,[z69,z2,z26,z4,z5,z12]),(0,[z1,z2,z3,z4,z5,z1328]),(0,[z1,z2,z3,z4,z145,z212])],[(0,[z1,z2,z3,z4,z5,z1329])],[(0,[z90,z2,z3,z4,z5,z747]),(0,[z30,z2,z3,z4,z5,z70]),(0,[z1,z2,z3,z102,z5,z580])],[(0,[z54,z1,z297,z3,z5,z8]),(0,[z110,z2,z3,z4,z5,z25]),(0,[z1,z110,z2,z4,z142,z8]),(0,[z1,z3,z1330,z4,z5,z8])],[(0,[z1,z24,z638,z4,z5,z12]),(0,[z69,z2,z3,z4,z27,z25]),(0,[z1,z203,z3,z204,z120,z8]),(0,[z109,z110,z2,z4,z5,z12]),(0,[z1,z2,z630,z4,z5,z12])],[(0,[z1,z290,z3,z4,z5,z8]),(0,[z1,z218,z18,z3,z4,z5]),(0,[z1,z18,z3,z4,z296,z5]),(0,[z1,z2,z236,z4,z5,z25]),(0,[z1,z2,z3,z855,z5,z8]),(0,[z1,z2,z3,z1331,z5,z8]),(0,[z1,z46,z3,z43,z5,z491]),(0,[z1,z1332,z3,z4,z5,z8])],[(0,[z53,z2,z3,z106,z5,z25])],[(0,[z143,z24,z3,z4,z5,z8]),(0,[z1,z24,z33,z4,z5,z8]),(0,[z115,z2,z3,z4,z5,z427])],[(0,[z90,z24,z3,z4,z5,z70]),(0,[z110,z2,z3,z4,z5,z325]),(0,[z110,z2,z3,z4,z5,z374]),(0,[z1,z1333,z3,z4,z5,z8])],[(0,[z1334,z1,z18,z3,z4,z8]),(0,[z1,z2,z3,z4,z5,z513]),(0,[z1,z3,z4,z5,z25,z907]),(0,[z1,z2,z1335,z4,z5,z8])],[(0,[z1336,z1,z3,z4,z5,z8]),(0,[z1,z1337,z3,z4,z5,z8]),(0,[z1,z1338,z219,z3,z4,z5]),(0,[z187,z2,z463,z3,z5,z8]),(0,[z54,z1,z176,z4,z5,z12]),(0,[z1,z2,z3,z1339,z5,z8])],[(0,[z1,z68,z18,z3,z5,z12]),(0,[z1,z2,z3,z1340,z5,z8]),(0,[z1,z2,z1338,z3,z4,z5]),(0,[z1,z11,z176,z4,z5,z12]),(0,[z1,z2,z3,z5,z779,z8])],[(0,[z17,z1,z332,z3,z5,z8]),(0,[z1,z2,z3,z979,z4,z8]),(0,[z1,z2,z3,z5,z8,z730]),(0,[z1,z2,z236,z4,z5,z197])],[(0,[z1,z2,z3,z1341,z5,z8]),(0,[z53,z2,z3,z106,z5,z197]),(0,[z1,z42,z716,z4,z5,z8]),(0,[z110,z2,z38,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1342]),(0,[z1,z3,z59,z126,z28,z8])],[(0,[z2,z3,z789,z4,z5,z8]),(0,[z1,z290,z3,z4,z5,z25]),(0,[z1,z2,z3,z1331,z5,z25]),(0,[z1,z3,z5,z917,z304,z8])]],
   [[(0,[z1334,z1,z2,z3,z4,z8]),(0,[z338,z1,z3,z4,z19,z8]),(0,[z1,z2,z3,z4,z5,z1343]),(0,[z1,z1344,z3,z4,z5,z8])],[(0,[z1,z2,z3,z188,z45,z8]),(0,[z69,z2,z3,z4,z27,z12]),(0,[z130,z1,z176,z4,z5,z131]),(0,[z1,z1345,z3,z4,z5,z8])],[(0,[z1,z18,z3,z4,z5,z225]),(0,[z401,z1,z3,z4,z5,z443]),(0,[z1,z2,z236,z4,z5,z12]),(0,[z1,z2,z622,z57,z5,z8]),(0,[z1,z2,z446,z4,z5,z1159])],[(0,[z1,z18,z3,z4,z5,z1002]),(0,[z2,z26,z4,z5,z45,z12]),(0,[z1,z1346,z3,z4,z5,z8]),(0,[z53,z2,z3,z106,z5,z12]),(0,[z318,z1,z2,z4,z5,z12]),(0,[z1,z2,z3,z4,z1347,z8])],[(0,[z1,z18,z3,z91,z5,z8]),(0,[z1,z161,z3,z4,z5,z454]),(0,[z1,z2,z3,z4,z5,z1348])],[(0,[z1,z24,z3,z473,z5,z8]),(0,[z502,z2,z3,z4,z5,z252]),(0,[z110,z2,z3,z410,z5,z8])],[(0,[z0,z2,z26,z4,z5,z8]),(0,[z1,z2,z3,z4,z308,z52]),(0,[z1,z161,z458,z4,z5,z8]),(0,[z1,z2,z458,z4,z5,z1154]),(0,[z1,z2,z3,z4,z140,z634]),(0,[z1275,z1,z3,z5,z304,z8])],[(0,[z1,z2,z3,z1349,z5,z8]),(0,[z1,z1204,z3,z4,z5,z8]),(0,[z1,z2,z1350,z4,z5,z8]),(0,[z2,z3,z36,z855,z5,z8]),(0,[z1,z2,z1351,z4,z5,z8]),(0,[z1,z3,z4,z5,z8,z1352]),(0,[z83,z1,z3,z62,z5,z8])],[(0,[z1,z2,z3,z1353,z5,z8]),(0,[z1,z150,z3,z4,z385,z8]),(0,[z1,z1354,z3,z4,z5,z8]),(0,[z1,z121,z3,z4,z5,z195])],[(0,[z1,z2,z3,z994,z5,z8]),(0,[z1,z254,z3,z4,z5,z197]),(0,[z1,z3,z4,z5,z1355,z8]),(0,[z1,z2,z4,z5,z374,z12]),(0,[z1356,z1,z3,z4,z5,z8])],[(0,[z289,z18,z3,z4,z5,z252]),(0,[z2,z3,z4,z5,z252,z747]),(0,[z1,z48,z3,z4,z5,z8]),(0,[z1,z1357,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z1358]),(0,[z1,z18,z3,z5,z120,z8]),(0,[z0,z150,z26,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1359]),(0,[z1,z2,z56,z321,z5,z8]),(0,[z1,z290,z3,z4,z5,z12])],[(0,[z1,z24,z3,z4,z5,z265]),(0,[z1,z24,z3,z4,z5,z491]),(0,[z1,z2,z3,z4,z1360,z8]),(0,[z1,z2,z3,z1361,z5,z8]),(0,[z1,z1362,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1363]),(1,[z1,z2,z769,z5,z8])],[(0,[z1,z2,z3,z296,z5,z120])],[(0,[z1,z288,z3,z4,z5,z8]),(0,[z1,z2,z129,z4,z5,z74]),(0,[z1,z2,z1364,z4,z5,z8]),(0,[z2,z3,z4,z5,z747,z70]),(0,[z1,z2,z3,z4,z5,z1365]),(0,[z1,z2,z3,z141,z5,z293]),(0,[z1,z2,z3,z4,z5,z1366]),(0,[z1,z1333,z3,z4,z5,z12]),(0,[z1,z2,z3,z4,z5,z1367])],[(0,[z1,z2,z3,z4,z1368,z8]),(0,[z0,z2,z26,z4,z5,z25]),(0,[z542,z1,z2,z3,z5,z178])]],
   [[(0,[z1,z24,z3,z15,z5,z8]),(0,[z1,z288,z3,z4,z5,z221]),(0,[z37,z2,z3,z4,z966,z8]),(0,[z292,z1,z2,z4,z5,z12]),(1,[z1,z2,z4,z717,z5]),(0,[z191,z1,z2,z769,z5,z8])],[(0,[z105,z1,z2,z787,z4,z5]),(0,[z1,z24,z3,z4,z5,z52]),(0,[z1,z2,z3,z602,z5,z8]),(0,[z1,z273,z3,z91,z5,z8]),(0,[z1,z2,z3,z4,z5,z903]),(0,[z1,z3,z232,z4,z5,z316])],[(0,[z1,z42,z11,z239,z5,z8]),(0,[z641,z2,z3,z4,z5,z555])],[(0,[z1,z18,z3,z4,z5,z316]),(0,[z37,z2,z3,z4,z45,z8]),(0,[z1,z2,z3,z4,z1369,z5]),(0,[z1,z2,z3,z4,z5,z1370]),(0,[z1,z48,z3,z4,z5,z25]),(0,[z1,z2,z1371,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z1372]),(0,[z1373,z2,z3,z4,z5,z8]),(0,[z1,z1374,z3,z4,z5,z8])],[(0,[z105,z24,z18,z3,z4,z5]),(0,[z24,z300,z3,z4,z5,z8]),(0,[z54,z1,z2,z3,z5,z328]),(0,[z1,z1375,z3,z4,z5,z8])],[(0,[z1,z1376,z3,z4,z5,z8]),(0,[z1377,z1,z3,z4,z5,z8]),(0,[z1,z2,z560,z4,z5,z12])],[(0,[z1,z24,z3,z5,z8,z23]),(0,[z1,z2,z196,z4,z34,z8]),(0,[z1,z288,z3,z4,z5,z25]),(0,[z1,z1378,z3,z4,z5,z8])],[(0,[z412,z1,z2,z4,z5,z12]),(0,[z1,z2,z393,z4,z298,z8]),(0,[z1,z2,z3,z239,z5,z361]),(0,[z1,z48,z3,z4,z5,z374])],[(0,[z1,z18,z10,z4,z5,z25]),(0,[z1,z2,z3,z867,z5,z8]),(0,[z0,z205,z26,z4,z5,z8]),(0,[z61,z1,z3,z59,z28,z8]),(0,[z1,z2,z3,z4,z742,z32])],[(0,[z1379,z1,z3,z4,z5,z8]),(0,[z1,z2,z3,z602,z5,z25]),(0,[z1,z2,z3,z4,z5,z1380]),(0,[z1,z2,z3,z59,z28,z60]),(0,[z1,z1381,z3,z4,z5,z8])],[(0,[z17,z1,z68,z3,z5,z8]),(0,[z1,z24,z3,z4,z5,z1310]),(0,[z0,z2,z26,z4,z5,z12]),(0,[z1,z2,z3,z4,z5,z1382]),(0,[z1022,z1,z75,z3,z5,z8])],[(0,[z1,z24,z218,z3,z4,z5]),(0,[z1,z18,z4,z428,z5,z8]),(0,[z17,z1,z2,z218,z3,z5]),(0,[z110,z24,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z1383,z8]),(0,[z37,z2,z3,z4,z45,z25]),(0,[z1,z2,z434,z4,z5,z25])],[(0,[z1,z88,z3,z4,z5,z328]),(0,[z1,z2,z245,z91,z5,z8]),(0,[z90,z2,z393,z4,z5,z70]),(0,[z1384,z2,z3,z4,z5,z8])],[(0,[z1,z2,z26,z4,z5,z12]),(0,[z872,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1385]),(0,[z1,z203,z3,z4,z204,z293]),(0,[z1356,z1,z3,z4,z5,z12])],[(0,[z1,z1386,z3,z4,z5,z8]),(0,[z1,z48,z3,z4,z5,z12]),(0,[z1,z1387,z3,z4,z5,z8])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 490) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 490).take 493) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 983).take 482) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1465)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [490, 493, 482] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 121).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 121).take 121).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 242).take 112).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 354).take 116).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 470).take 42).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [121, 121, 112, 116, 42] = true :=
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

end PEqualNP.Outside.L_meta_37923

theorem PEqualNP.Outside.L_meta_37923 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074666 * 2 ^ 32 + 4276812448) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074666 * 2 ^ 32 + 4276812448) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_37923.solve