import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_40764

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
  Nat.testBit (4276808384 * 2 ^ 32 + 4274571456) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x2006b1af301c71e5#64 ++ 0x0400d635e6038e3c#64 ++ 0xa04ff3ff303cf3e6#64 ++ 0xf409fe7fe6079e7c#64 : BitVec 256),
   (0x0191846140c1a6ae#64 ++ 0x0032308c281834d5#64 ++ 0xe3b18c63c1c7fffd#64 ++ 0xfc76318c7838ffff#64 : BitVec 256),
   (0x0c2e0b82b6061850#64 ++ 0x0185c17056c0c30a#64 ++ 0xdc3e0f83fe071c7b#64 ++ 0xfb87c1f07fc0e38f#64 : BitVec 256),
   (0x56c00ed41b681f00#64 ++ 0x0ad801da836d03e0#64 ++ 0xffc00ffc3ff81f87#64 ++ 0xbff801ff87ff03f0#64 : BitVec 256),
   (0x9b7b50002db7c000#64 ++ 0x136f6a0005b6f800#64 ++ 0xfffff0003fffe007#64 ++ 0xdffffe0007fffc00#64 : BitVec 256),
   (0x1ffdef7bc0000000#64 ++ 0x23ffbdef78000000#64 ++ 0x1fffffffc0000007#64 ++ 0xe3fffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [3, 4]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [2, 9]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [8, 11]⟩, ⟨.or, [12, 10]⟩, ⟨.or, [9, 5]⟩, ⟨.and, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0191846140c1a6ae 0x0032308c281834d5 0xe3b18c63c1c7fffd 0xfc76318c7838ffff

def z1 : W := mkw 0x0c2e0b82b6061850 0x0185c17056c0c30a 0xdc3e0f83fe071c7b 0xfb87c1f07fc0e38f

def z2 : W := mkw 0x1ffdef7bc0000000 0x23ffbdef78000000 0x1fffffffc0000007 0xe3fffffff8000000

def z3 : W := mkw 0x1ffdef7bc0c1a6ae 0x23ffbdef781834d5 0x3fffffffc1c0e387 0xe7fffffff8381c70

def z4 : W := mkw 0x2006b1af301c71e5 0x0400d635e6038e3c 0xa04ff3ff303cf3e6 0xf409fe7fe6079e7c

def z5 : W := mkw 0x56c00ed41b681f00 0x0ad801da836d03e0 0xffc00ffc3ff81f87 0xbff801ff87ff03f0

def z6 : W := mkw 0x9b7b50002db7c000 0x136f6a0005b6f800 0xfffff0003fffe007 0xdffffe0007fffc00

def z7 : W := mkw 0x2000b0ad101871a5 0x04001615a2030e34 0xa041f3fc3038f386 0xb4083e7f86071e70

def z8 : W := mkw 0x5eea0ed43f6e1f00 0x0bdd41da87edc3e0 0xfffe0ffc3fff1f87 0xffffc1ff87ffe3f0

def z9 : W := mkw 0x0191846140818000 0x0032308c28103000 0xe3b18c63c1c7e005 0xfc76318c7838fc00

def z10 : W := mkw 0x0000000000000000 0x0000000000000000 0xc000000000071c78 0x180000000000e38f

def z11 : W := mkw 0x0191846140c1a6ae 0x0032308c281834d5 0x2381806001c0e384 0x0470300c00381c70

def z12 : W := mkw 0x04000a8012001800 0x0080015002400300 0xdc000f803e001c03 0xbb8001f007c00380

def z13 : W := mkw 0x16c00e5000000000 0x02d801ca00000000 0x1fc00ffc00000007 0xa3f801ff80000000

def z14 : W := mkw 0x800210002db7c000 0x1000420005b6f800 0xe00000003fffe000 0x1c00000007fffc00

def z15 : W := mkw 0x04020a8036061850 0x0080415006c0c30a 0xdc000f803e071c7b 0xbb8001f007c0e38f

def z16 : W := mkw 0xdff94ed41feb9f00 0x1bff29da83fd73e0 0xfff00ffc3ffb1f87 0xbffe01ff87ff63f0

def z17 : W := mkw 0x44800ed412481f00 0x089001da824903e0 0xa0400ffc30381f86 0xb40801ff860703f0

def z18 : W := mkw 0x00008021000020a4 0x0000100420000414 0x00000063000013e0 0x2000000c6000027c

def z19 : W := mkw 0x400000841b681f00 0x08000010836d03e0 0xe00000003ff81f80 0x1c00000007ff03f0

def z20 : W := mkw 0x20021084301c71e5 0x0400421086038e3c 0xa04003fc303cf3e6 0xb408007f86079e7c

def z21 : W := mkw 0x1e6c6b1a80000000 0x23cd8d6350000000 0x1c4e739c00000002 0x0389ce7380000000

def z22 : W := mkw 0x1ffdef7bc0c1a6ae 0x23ffbdef781834d5 0xffffffffc1c7ffff 0xfffffffff838ffff

def z23 : W := mkw 0x04040b8292001850 0x008081705240030a 0x00000f83c0001c78 0x200001f07800038f

def z24 : W := mkw 0x20021084361e79f5 0x0400421086c3cf3e 0xe00000003e3ffff8 0x1c00000007c7ffff

def z25 : W := mkw 0x0004a12b00000000 0x0000942560000000 0x004ff3ff00000006 0xe009fe7fe0000000

def z26 : W := mkw 0x9f7f5b82bfb7d850 0x13efeb7057f6fb0a 0xffffff83fffffc7f 0xfffffff07fffff8f

def z27 : W := mkw 0x9bfbd4616df7e6ae 0x137f7a8c2dbefcd5 0xfffffc63ffffffff 0xffffff8c7fffffff

def z28 : W := mkw 0x0002008036061850 0x0000401006c0c30a 0xc00000003e071c78 0x1800000007c0e38f

def z29 : W := mkw 0x52c0045409680700 0x0a58008a812d00e0 0x23c0007c01f80384 0x0478000f803f0070

def z30 : W := mkw 0x56400a941b281900 0x0ac8015283650320 0x1c40039c3e380002 0x0388007387c70000

def z31 : W := mkw 0x1fffeffbf6061850 0x23fffdff7ec0c30a 0xdffffffffe071c7f 0xfbffffffffc0e38f

def z32 : W := mkw 0x0002100020144000 0x0000420004028800 0xa04ff000303ce006 0xd409fe0006079c00

def z33 : W := mkw 0x20021084301c71e5 0x0400421086038e3c 0xa0000000303cf3e0 0x1400000006079e7c

def z34 : W := mkw 0x5ffdefffdb681f00 0x2bffbdfffb6d03e0 0xfffffffffff81f87 0xffffffffffff03f0

def z35 : W := mkw 0x1ff94e5000000000 0x03ff29ca00000000 0x1ffffffc00000007 0xe3ffffff80000000

def z36 : W := mkw 0xdff94e500fe38e00 0x1bff29ca01fc71c0 0x5fb00c000fc30c01 0x0bf6018001f86180

def z37 : W := mkw 0xdffb5ed43fffdf00 0x1bff6bda87fffbe0 0xfffffffc3fffff87 0xffffffff87fffff0

def z38 : W := mkw 0x2004a1af100831e5 0x04009435e201063c 0xa00183ff0004f3e4 0xf400307fe0009e7c

def z39 : W := mkw 0x2c2ebbafb61e79f5 0x0585d775f6c3cf3e 0xfc7ffffffe3fffff 0xff8fffffffc7ffff

def z40 : W := mkw 0x09394000c0000000 0x2127280018000000 0x00300000c0000000 0x0006000018000000

def z41 : W := mkw 0x9ffb5e50edb7c000 0x33ff6bca1db6f800 0xfffffc00ffffe007 0xdfffff801ffffc00

def z42 : W := mkw 0x1e684a1080000000 0x23cd094210000000 0x1c00000000000000 0x0380000000000000

def z43 : W := mkw 0x9bf944404de3860a 0x137f288809bc70c1 0x5fb00c00cfc30c19 0x0bf6018019f86183

def z44 : W := mkw 0x20000084100831e5 0x040000108201063c 0x00000000000013e0 0x000000000000027c

def z45 : W := mkw 0x1b79400000000000 0x036f280000000000 0x1ffff00000000007 0xc3fffe0000000000

def z46 : W := mkw 0x9fffff7bedb7c000 0x33ffffef7db6f800 0xffffffffffffe007 0xfffffffffffffc00

def z47 : W := mkw 0x9f7f4b82bfa79850 0x13efe97057f4f30a 0xdfbe0f83ffc71c7b 0xfbf7c1f07ff8e38f

def z48 : W := mkw 0x44800ed412481f00 0x089001da824903e0 0x00000ffc00001f80 0x200001ff800003f0

def z49 : W := mkw 0x1b79400000818000 0x036f280000103000 0xfffff00001c7e007 0xdffffe000038fc00

def z50 : W := mkw 0xdffbdef57fffffae 0x1bff7bdeaffffff5 0xffffffffffffffff 0xffffffffffffffff

def z51 : W := mkw 0x5fffefffff6e1f50 0x2bfffdffffedc3ea 0xffffffffffff1fff 0xffffffffffffe3ff

def z52 : W := mkw 0x36c6bfff301c71e5 0x06d8d7ffe6038e3c 0xbfcfffff303cf3e7 0xf7f9ffffe6079e7c

def z53 : W := mkw 0x00808461004026a4 0x0010108c200804d4 0xe3818c6301c4ffe5 0xfc70318c60389ffc

def z54 : W := mkw 0x76c6bfff3b7c7fe5 0x0ed8d7ffe76f8ffc 0xffcfffff3ffcffe7 0xfff9ffffe7ff9ffc

def z55 : W := mkw 0x76c4afff1b683fe5 0x0ed895ffe36d07fc 0xffc00fff3ff81fe7 0xbff801ffe7ff03fc

def z56 : W := mkw 0x1ff94e50c0c1860a 0x23ff29ca181830c1 0x5fb00c00c1c30c19 0x0bf6018018386183

def z57 : W := mkw 0x00008021000020a4 0x0000100420000414 0xa00180630004f3e4 0xf400300c60009e7c

def z58 : W := mkw 0x2006318e301c5141 0x0400c631c6038a28 0x004e739c30380002 0x0009ce7386070000

def z59 : W := mkw 0x57d18ef55be9bfae 0x0afa31deab7d37f5 0xfff18fffffffffff 0xfffe31ffffffffff

def z60 : W := mkw 0x00008021000020a4 0x0000100420000414 0xe0318c63c007fffd 0xfc06318c7800ffff

def z61 : W := mkw 0x1ffd4f52c0000000 0x23ffa9ea58000000 0x1fbe0f83c0000003 0xe3f7c1f078000000

def z62 : W := mkw 0x13d1e47940c1a6ae 0x227a3c8f281834d5 0x23c1f07c01c0e384 0x04783e0f80381c70

def z63 : W := mkw 0x2006318e301c5141 0x0400c631c6038a28 0xa04ff39c303ce006 0xd409fe7386079c00

def z64 : W := mkw 0x04040b0280000000 0x0080816050000000 0x00000f83c0000000 0x200001f078000000

def z65 : W := mkw 0x0002008030041040 0x0000401006008208 0x8000000030041060 0x100000000600820c

def z66 : W := mkw 0x0c280a0086020810 0x0185014010c04102 0x5c300c00ce030c19 0x0b86018019c06183

def z67 : W := mkw 0x293ff12be01460e5 0x2527fe257c028c1c 0x003ff003c004e060 0x4007fe0078009c0c

def z68 : W := mkw 0x5ff94ed41b681f00 0x0bff29da836d03e0 0xfffffffc3ff81f87 0xffffffff87ff03f0

def z69 : W := mkw 0x2000b02d001861a5 0x04001605a0030c34 0x2041f07c0038e384 0x04083e0f80071c70

def z70 : W := mkw 0x1eecef7bc0000000 0x23dd9def78000000 0x1c4e7fffc0000002 0x2389cffff8000000

def z71 : W := mkw 0x5ee80e508f620e10 0x0bdd01ca11ec41c2 0x5fb00c00cfc30c19 0x0bf6018019f86183

def z72 : W := mkw 0x2406bbafb21c79f5 0x0480d775f6438f3e 0xa04ffffff03cfffe 0xf409fffffe079fff

def z73 : W := mkw 0x2006b12b201460e5 0x0400d62564028c1c 0x004ff3ff0004e066 0xe009fe7fe0009c0c

def z74 : W := mkw 0x0484af7bc0000000 0x209095ef78000000 0x00000fffc0000000 0x200001fff8000000

def z75 : W := mkw 0x0d3f8ba3f687b8fe 0x01a7f1747ed0f71f 0xdc3f8f83fe07fc7b 0xfb87f1f07fc0ff8f

def z76 : W := mkw 0x09bde56bc0000000 0x2137bcad78000000 0x03bffc63c0000005 0xe077ff8c78000000

def z77 : W := mkw 0x093de12bc0000000 0x2127bc2578000000 0x003ff003c0000000 0x4007fe0078000000

def z78 : W := mkw 0x9b7b50002db7c000 0x136f6a0005b6f800 0x5fbff0000fc7e001 0x4bf7fe0001f8fc00

def z79 : W := mkw 0x2006b12b201460e5 0x0400d62564028c1c 0x000ff0030004e060 0x4001fe0060009c0c

def z80 : W := mkw 0x56c00e500b600e00 0x0ad801ca016c01c0 0x5f800c000fc00c01 0x0bf0018001f80180

def z81 : W := mkw 0x9b7940000da38000 0x136f280001b47000 0x5fb000000fc30001 0x0bf6000001f86000

def z82 : W := mkw 0x13d1846149e1a6ae 0x027a308c293c34d5 0xfff18c63ffffffff 0xfffe318c7fffffff

def z83 : W := mkw 0x9b7940000da38000 0x136f280001b47000 0xfff000003ffb0007 0x9ffe000007ff6000

def z84 : W := mkw 0x2197b5ef70ddf7ef 0x0432f6bdee1bbefd 0xe3fffffff1ffffff 0xfc7ffffffe3fffff

def z85 : W := mkw 0x0828000084020010 0x0105000010804002 0x00300000c0030018 0x0006000018006003

def z86 : W := mkw 0x2000a02d000821a5 0x04001405a0010434 0x0000007c00000380 0x0000000f80000070

def z87 : W := mkw 0x819394616df7e6ae 0x1032728c2dbefcd5 0xe3b18c63fffffffd 0xfc76318c7fffffff

def z88 : W := mkw 0x1242100029344000 0x0248420005268800 0xffcff0003ffce007 0xdff9fe0007ff9c00

def z89 : W := mkw 0x0006018230041040 0x0000c03046008208 0xc03e0f83f0071c7b 0xf807c1f07e00e38f

def z90 : W := mkw 0x1ff94e50c0000000 0x23ff29ca18000000 0x1fb00c00c0000001 0x03f6018018000000

def z91 : W := mkw 0x3ffffffff01c71e5 0x27fffffffe038e3c 0xbffffffff03cf3e7 0xf7fffffffe079e7c

def z92 : W := mkw 0x0939400000000000 0x0127280000000000 0x003ff00000000000 0x4007fe0000000000

def z93 : W := mkw 0xd6c21ed43fffdf00 0x1ad843da87fffbe0 0xffc00ffc3fffff87 0xbff801ff87fffff0

def z94 : W := mkw 0x000681a3300430e4 0x0000d0346600861c 0xa00f83e33004f3e6 0xf401f07c66009e7c

def z95 : W := mkw 0x20021084301c5141 0x0400421086038a28 0x0000000030380000 0x0000000006070000

def z96 : W := mkw 0x011180214081a0ae 0x0022300428103415 0x00318003c007e078 0x400630007800fc0f

def z97 : W := mkw 0x0191044040c1a6ae 0x00322088081834d5 0xe3b00c00c1c7fff9 0x1c7601801838ffff

def z98 : W := mkw 0x1b79400000000000 0x036f280000000000 0x1fb0000000000001 0x03f6000000000000

def z99 : W := mkw 0x5eee0fd6bf6e1f50 0x0bddc1fad7edc3ea 0xffce0ffc3ff81f87 0xbff9c1ff87ff03f0

def z100 : W := mkw 0x0195a56b40000000 0x0032b4ad68000000 0x03ffffffc0000007 0xe07ffffff8000000

def z101 : W := mkw 0x1f7deb3bc0000000 0x23efbd6778000000 0x1c7ff39fc0000002 0x438ffe73f8000000

def z102 : W := mkw 0x12c0044009600600 0x02580088012c00c0 0xffc00c603ff81f87 0xbff8018c07ff03f0

def z103 : W := mkw 0x082a000024060000 0x010540000480c000 0xdc3e00003e070003 0xdb87c00007c0e000

def z104 : W := mkw 0x1240000009200000 0x0248000001240000 0xffc000003ff80007 0x9ff8000007ff0000

def z105 : W := mkw 0x3ffdefffd00831e5 0x27ffbdfffa01063c 0x1fffffffc00013e7 0xe3fffffff800027c

def z106 : W := mkw 0x9351500009b1c000 0x126a2a0001363800 0xe3f1f00001ffe005 0xdc7e3e00003ffc00

def z107 : W := mkw 0x5ffdefffdbe9bfae 0x2bffbdfffb7d37f5 0xffffffffffffffff 0xffffffffffffffff

def z108 : W := mkw 0x0006018230041040 0x0000c03046008208 0x800e038330041062 0xf001c0706600820c

def z109 : W := mkw 0x0000008410081100 0x0000001082010220 0xa04003fc30381386 0xb408007f86070270

def z110 : W := mkw 0x2006310a20144041 0x0400c62144028808 0x000e700000000000 0x0001ce0000000000

def z111 : W := mkw 0x4000000409680700 0x08000000812d00e0 0x2000000001f80380 0x04000000003f0070

def z112 : W := mkw 0xdbfb54542dffc700 0x1b7f6a8a85bff8e0 0xfffff07c3fffe387 0xdffffe0f87fffc70

def z113 : W := mkw 0x093f8123e487a0fe 0x0127f0247c90f41f 0x003f8003c007e078 0x4007f0007800fc0f

def z114 : W := mkw 0x0191044040c1860a 0x00322088081830c1 0x43b00c00c1c30c19 0x0876018018386183

def z115 : W := mkw 0x9351500009b1c000 0x126a2a0001363800 0x23c1f00001f8e004 0x04783e00003f1c00

def z116 : W := mkw 0x0000008410081100 0x0000001082010220 0xa000000030381380 0x1400000006070270

def z117 : W := mkw 0xbb7b50843dbff1e5 0x176f6a1087b7fe3c 0xfffff0003ffff3e7 0xdffffe0007fffe7c

def z118 : W := mkw 0x2004a1af100831e5 0x04009435e201063c 0x000003ff000013e0 0x2000007fe000027c

def z119 : W := mkw 0x01918461404026ae 0x0032308c280804d5 0x03b18c63c0001ffd 0xe076318c780003ff

def z120 : W := mkw 0x1240008419281100 0x0248001083250220 0xffc003fc3ff81387 0xbff8007f87ff0270

def z121 : W := mkw 0x1ffdef7bc9200000 0x23ffbdef79240000 0xfffffffffff80007 0xffffffffffff0000

def z122 : W := mkw 0x093b000024878000 0x012760000490f000 0xffbf80003fc7e007 0xdff7f00007f8fc00

def z123 : W := mkw 0x0080044000400600 0x00100088000800c0 0xe3800c6001c01f85 0xbc70018c003803f0

def z124 : W := mkw 0x9b7bd0216db7e0ae 0x136f7a042db6fc15 0xfffff003ffffe07f 0xdffffe007ffffc0f

def z125 : W := mkw 0x0191846140c1a6ae 0x0032308c281834d5 0x63b18c60c1c3ef9d 0x0c76318c18387df3

def z126 : W := mkw 0x0c2eababb6061850 0x0185d57576c0c30a 0xdc7ffffffe071c7f 0xfb8fffffffc0e38f

def z127 : W := mkw 0x0000000000000000 0x0000000000000000 0x004003fc00000006 0xa008007f80000000

def z128 : W := mkw 0x3246b1af393c71e5 0x0648d635e7278e3c 0xffcff3ff3ffcf3e7 0xfff9fe7fe7ff9e7c

def z129 : W := mkw 0x44800ed412481f00 0x089001da824903e0 0xe3800ffc01c01f85 0xbc7001ff803803f0

def z130 : W := mkw 0x9f7b5a00afb7c810 0x13ef6b4015f6f902 0xfffffc00ffffec1f 0xdfffff801ffffd83

def z131 : W := mkw 0x09bb846164c7a6ae 0x0137708c2c98f4d5 0xffbf8c63ffc7ffff 0xfff7f18c7ff8ffff

def z132 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z133 : W := mkw 0x6486bfff325c7fe5 0x0c90d7ffe64b8ffc 0xa04fffff303cffe6 0xf409ffffe6079ffc

def z134 : W := mkw 0x13d1e47940c1a6ae 0x227a3c8f281834d5 0xe3f1fc7fc1c7fffd 0xfc7e3f8ff838ffff

def z135 : W := mkw 0x0dbf8fe3f6061850 0x01b7f1fc7ec0c30a 0xdfbf8fe3fe071c7f 0xfbf7f1fc7fc0e38f

def z136 : W := mkw 0x0111000000818000 0x0022200000103000 0xe3b1800001c7e005 0xdc7630000038fc00

def z137 : W := mkw 0x2004a1af100831e5 0x04009435e201063c 0x004ff3ff000013e6 0xe009fe7fe000027c

def z138 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0300c03c0071c79 0xf80601807800e38f

def z139 : W := mkw 0x9b7b50002db7c000 0x136f6a0005b6f800 0x5ffe70003ffb0003 0x0bffce0007ff6000

def z140 : W := mkw 0x0c280a0086020810 0x0185014010c04102 0xdc300c03ce071c79 0xfb86018079c0e38f

def z141 : W := mkw 0x20001004001861a5 0x0400020080030c34 0x200000000038e380 0x0400000000071c70

def z142 : W := mkw 0xffffffff3fffffe5 0x1fffffffe7fffffc 0xffffffff3fffffe7 0xffffffffe7fffffc

def z143 : W := mkw 0x00808461404026ae 0x0010108c280804d5 0x0000006000000380 0x0000000c00000070

def z144 : W := mkw 0x1240000009200000 0x0248000001240000 0x23c0000001f80004 0x04780000003f0000

def z145 : W := mkw 0x1e6c6b1a80000000 0x23cd8d6350000000 0x1c7e7f9fc0000003 0xe38fcff3f8000000

def z146 : W := mkw 0x2006318e301c5141 0x0400c631c6038a28 0xa04e73fc30381386 0xb409ce7f86070270

def z147 : W := mkw 0x893b50002497c000 0x11276a000492f800 0xa07ff000303fe006 0xd40ffe000607fc00

def z148 : W := mkw 0x0002008036c7befe 0x0000401006d8f7df 0xe00000003fc7fff8 0x1c00000007f8ffff

def z149 : W := mkw 0x57d18ef55be9bfae 0x0afa31deab7d37f5 0xffc18ffc3ff8ff87 0xbff831ff87ff1ff0

def z150 : W := mkw 0x0191846140c1a6ae 0x0032308c281834d5 0x23818c63c1c0fffc 0x2470318c78381fff

def z151 : W := mkw 0x56c00ed41b681f00 0x0ad801da836d03e0 0xfff00fffffff1fff 0xfffe01ffffffe3ff

def z152 : W := mkw 0x9bfbf4796db7c000 0x337f7e8f2db6f800 0xfffff07c3fffe007 0xdffffe0f87fffc00

def z153 : W := mkw 0x76c0befd1b787fa5 0x0ed817dfa36f0ff4 0xffc1fffc3ff8ff87 0xbff83fff87ff1ff0

def z154 : W := mkw 0x09bf8563e4c7a6fe 0x0137f0ac7c98f4df 0xe3bf8c63c1c7fffd 0xfc77f18c7838ffff

def z155 : W := mkw 0x0c2a0a80b6061850 0x0185415016c0c30a 0xdc300c00fe071c79 0x1b8601801fc0e38f

def z156 : W := mkw 0x0c2e1b82b6165850 0x0185c37056c2cb0a 0xfc7fff83fe3ffc7f 0xff8ffff07fc7ff8f

def z157 : W := mkw 0x8d3f5b82b697d850 0x11a7eb7056d2fb0a 0xdc3fff83fe07fc7b 0xfb87fff07fc0ff8f

def z158 : W := mkw 0x0004a12b000020a4 0x0000942560000414 0xa04ff3ff0004f3e6 0xf409fe7fe0009e7c

def z159 : W := mkw 0x0111000000c1a6ae 0x00222000001834d5 0xe3b1800001c7fffd 0xdc7630000038ffff

def z160 : W := mkw 0x0000000000c1a6ae 0x00000000001834d5 0xe000000001c7fff8 0x1c0000000038ffff

def z161 : W := mkw 0xba6ef1af3d3e71e5 0x174dde35e7a7ce3c 0xbc4ff3ff3e3cf3e6 0xf789fe7fe7c79e7c

def z162 : W := mkw 0x2006b12f201c61e5 0x0400d625e4038c3c 0x204ff07f003ce3e4 0x4409fe0fe0079c7c

def z163 : W := mkw 0x76c21ed43b7c7fe5 0x0ed843da876f8ffc 0xffc00ffc3ffcffe7 0xbff801ff87ff9ffc

def z164 : W := mkw 0x082e0102a4060050 0x0105c0205480c00a 0x003e0003c0070078 0x4007c0007800e00f

def z165 : W := mkw 0x0595af7bc0c1a6ae 0x20b2b5ef781834d5 0xe3b18fffc1c7fffd 0xfc7631fff838ffff

def z166 : W := mkw 0x0dbf8fe3f6c7befe 0x01b7f1fc7ed8f7df 0xffbf8fe3ffc7ffff 0xfff7f1fc7ff8ffff

def z167 : W := mkw 0x0080044000400600 0x00100088000800c0 0x2380006001c00384 0x0470000c00380070

def z168 : W := mkw 0x00808461404026ae 0x0010108c280804d5 0x00000c63c0001ff8 0x2000018c780003ff

def z169 : W := mkw 0x0004210a00000000 0x0000842140000000 0x004e739c00000002 0x0009ce7380000000

def z170 : W := mkw 0x082a008036061850 0x0105401006c0c30a 0xdc3e00003e071c7b 0xdb87c00007c0e38f

def z171 : W := mkw 0x3ffffffff0ddf7ef 0x27fffffffe1bbefd 0xfffffffff1ffffff 0xfffffffffe3fffff

def z172 : W := mkw 0x1ff9ce71c0c1a6ae 0x23ff39ce381834d5 0xffb18c63c1c7fffd 0xfff6318c7838ffff

def z173 : W := mkw 0x2006b1af301c71e5 0x0400d635e6038e3c 0xe07ffffff03fffff 0xfc0ffffffe07ffff

def z174 : W := mkw 0x1a68400000000000 0x034d080000000000 0x1c4e700000000002 0x0389ce0000000000

def z175 : W := mkw 0x1fffef7be4060050 0x23fffdef7c80c00a 0x1fffffffc007007f 0xe3fffffff800e00f

def z176 : W := mkw 0x56c00e5409680700 0x0ad801ca812d00e0 0x3fc00ffc01f80387 0xa7f801ff803f0070

def z177 : W := mkw 0xbffffffffdbff1e5 0x37ffffffffb7fe3c 0xfffffffffffff3e7 0xfffffffffffffe7c

def z178 : W := mkw 0x1f7f4b82b6061850 0x03efe97056c0c30a 0xdfffff83fe071c7f 0xfbfffff07fc0e38f

def z179 : W := mkw 0x800210002d364000 0x1000420005a6c800 0x000000003e380000 0x0000000007c70000

def z180 : W := mkw 0x9bfb54406df7c60a 0x137f6a880dbef8c1 0xfffffc00ffffec1f 0xdfffff801ffffd83

def z181 : W := mkw 0x57d10e504be18e0a 0x0afa21ca097c31c1 0x5fb00c00cfc30c19 0x0bf6018019f86183

def z182 : W := mkw 0x56c4afff1b681f00 0x0ad895ffe36d03e0 0xffcfffff3ff81f87 0xfff9ffffe7ff03f0

def z183 : W := mkw 0x0080846140c1a6ae 0x0010108c281834d5 0xe0000c63c1c7fff8 0x3c00018c7838ffff

def z184 : W := mkw 0x0c2e0b82b6061850 0x0185c17056c0c30a 0x1c0e03803e000002 0x0381c07007c00000

def z185 : W := mkw 0x9a6a50002d364000 0x134d4a0005a6c800 0x1c4e70003e380002 0x0389ce0007c70000

def z186 : W := mkw 0x1ffdef7bc0000000 0x23ffbdef78000000 0x1fbffc03c0000001 0x43f7ff8078000000

def z187 : W := mkw 0x00021084301c5100 0x0000421086038a20 0xa04ff3fc303cf386 0xf409fe7f86079e70

def z188 : W := mkw 0x0484af7bc04026ae 0x209095ef780804d5 0x00000fffc0001ff8 0x200001fff80003ff

def z189 : W := mkw 0x56c08ef55b683fae 0x0ad811deab6d07f5 0xffc00ffffff81fff 0xbff801ffffff03ff

def z190 : W := mkw 0x019184614081a0ae 0x0032308c28103415 0x03b18c63c007e07d 0xe076318c7800fc0f

def z191 : W := mkw 0x0c2c0b0280000000 0x0185816050000000 0x1c0e038000000002 0x0381c07000000000

def z192 : W := mkw 0x3ffffffff01c5141 0x27fffffffe038a28 0x1ffffffff0380007 0xe3fffffffe070000

def z193 : W := mkw 0x56c00ed41b681f00 0x0ad801da836d03e0 0x23c00ffc01f81f84 0x247801ff803f03f0

def z194 : W := mkw 0x00808461404026ae 0x0010108c280804d5 0xa0018c63c004fffc 0xf400318c78009fff

def z195 : W := mkw 0x4cae0fd6b64e1f50 0x0995c1fad6c9c3ea 0xdc3e0ffffe071ffb 0xfb87c1ffffc0e3ff

def z196 : W := mkw 0xdfffffffffffdf00 0x3bfffffffffffbe0 0xffffffffffffff87 0xfffffffffffffff0

def z197 : W := mkw 0x2c2e3b8eb61e5951 0x0585c771d6c3cb2a 0xdc7e7f9ffe3f1c7b 0xfb8fcff3ffc7e38f

def z198 : W := mkw 0x44808ef552483fae 0x089011deaa4907f5 0x00000fffc0001ff8 0x200001fff80003ff

def z199 : W := mkw 0x00029021201460a4 0x0000520424028c14 0xa04ff063303cf3e6 0xf409fe0c66079e7c

def z200 : W := mkw 0x56c00ed41b681f00 0x0ad801da836d03e0 0x3fc003fc3ff80386 0x07f8007f87ff0070

def z201 : W := mkw 0x5240001409280100 0x0a48000281250020 0x0040001c00380000 0x0008000380070000

def z202 : W := mkw 0x76c63fde3b7c5f41 0x0ed8c7fbc76f8be8 0xffce7ffc3ff81f87 0xbff9cfff87ff03f0

def z203 : W := mkw 0x13d1e47940000000 0x227a3c8f28000000 0x03c1f07c00000004 0x00783e0f80000000

def z204 : W := mkw 0x2c2e3b8eb61e5951 0x0585c771d6c3cb2a 0x1c4e739c3e380002 0x0389ce7387c70000

def z205 : W := mkw 0x56c40fd69b681f50 0x0ad881fad36d03ea 0xffc00ffffff81fff 0xbff801ffffff03ff

def z206 : W := mkw 0xbb7ff1af3dbff1e5 0x176ffe35e7b7fe3c 0xfffff3ff3ffff3e7 0xfffffe7fe7fffe7c

def z207 : W := mkw 0x893b50002497c000 0x11276a000492f800 0x003ff0000007e000 0x4007fe000000fc00

def z208 : W := mkw 0x9fffff7be497c000 0x33ffffef7c92f800 0x1fffffffc007e007 0xe3fffffff800fc00

def z209 : W := mkw 0x0000008410081100 0x0000001082010220 0x0040039c30380002 0x0008007386070000

def z210 : W := mkw 0x882a500024164000 0x11054a000482c800 0x000e700000000000 0x0001ce0000000000

def z211 : W := mkw 0x2006b1ab301470e5 0x0400d63566028e1c 0x800ff3833004f062 0xf001fe7066009e0c

def z212 : W := mkw 0x0000000000000000 0x0000000000000000 0x004ff00000000006 0xc009fe0000000000

def z213 : W := mkw 0x1ffdef7bc0000000 0x23ffbdef78000000 0x1fcff3fc00000006 0x03f9fe7f80000000

def z214 : W := mkw 0x0002008036061850 0x0000401006c0c30a 0x000000003e000000 0x0000000007c00000

def z215 : W := mkw 0x093de12bc081a0ae 0x2127bc2578103415 0x003ff003c007e078 0x4007fe007800fc0f

def z216 : W := mkw 0x5eee0fd6bf6e1f50 0x0bddc1fad7edc3ea 0xfffe0fffffff1fff 0xffffc1ffffffe3ff

def z217 : W := mkw 0x04000a8012001800 0x0080015002400300 0x1c0003803e000002 0x0380007007c00000

def z218 : W := mkw 0x9a6a50002db7c000 0x134d4a0005b6f800 0xfc4e70003fffe002 0x1f89ce0007fffc00

def z219 : W := mkw 0x0c2cab2b80000000 0x0185956570000000 0x1c7fffffc0000007 0xe38ffffff8000000

def z220 : W := mkw 0x082e0102a4060050 0x0105c0205480c00a 0xdc3e0003fe07007b 0xdb87c0007fc0e00f

def z221 : W := mkw 0x0c2c0b0280000000 0x0185816050000000 0x1c3e0f83c0000003 0xe387c1f078000000

def z222 : W := mkw 0x2002108430ddf7ef 0x04004210861bbefd 0xe000000031fffff8 0x1c000000063fffff

def z223 : W := mkw 0x1351000009a18000 0x026a200001343000 0xfff180003fffe007 0xdffe300007fffc00

def z224 : W := mkw 0x04000a8412081900 0x0080015082410320 0xfc400ffc3e381f87 0xbf8801ff87c703f0

def z225 : W := mkw 0x0cae8fe3f6463efe 0x0195d1fc7ec8c7df 0xdc3e0fe3fe071ffb 0xfb87c1fc7fc0e3ff

def z226 : W := mkw 0x1f7d6b1a80000000 0x23efad6350000000 0x1ffff39c00000007 0xc3fffe7380000000

def z227 : W := mkw 0x3b7ff1af301c71e5 0x076ffe35e6038e3c 0xbffff3ff303cf3e7 0xf7fffe7fe6079e7c

def z228 : W := mkw 0x0c2e0b86b60e1950 0x0185c170d6c1c32a 0xfc7e0ffffe3f1fff 0xff8fc1ffffc7e3ff

def z229 : W := mkw 0x53d1847549e9a7ae 0x0a7a308ea93d34f5 0xe3f18c7fc1fffffd 0xfc7e318ff83fffff

def z230 : W := mkw 0x57d18e714be1aeae 0x0afa31ce297c35d5 0xffb18c63cfc7fffd 0xfff6318c79f8ffff

def z231 : W := mkw 0x04000a8012001800 0x0080015002400300 0x00000f8000001c00 0x200001f000000380

def z232 : W := mkw 0x0c2c0b0286020810 0x0185816050c04102 0x5c3e0f83ce030c1b 0xeb87c1f079c06183

def z233 : W := mkw 0x0dbdef7bc0000000 0x21b7bdef78000000 0x003fffffc0000000 0x6007fffff8000000

def z234 : W := mkw 0xde6a5a943f3e5900 0x1bcd4b5287e7cb20 0x1c4e739c3e380002 0x0389ce7387c70000

def z235 : W := mkw 0x2006b12b201460e5 0x0400d62564028c1c 0xa04ff003303ce066 0xd409fe0066079c0c

def z236 : W := mkw 0xdf7b5a943fbfd900 0x1bef6b5287f7fb20 0xfffff39c3fffe007 0xdffffe7387fffc00

def z237 : W := mkw 0x2006b1af361e79f5 0x0400d635e6c3cf3e 0xe04ff3ff3e3ffffe 0xfc09fe7fe7c7ffff

def z238 : W := mkw 0xbf7ffbafbfbff9f5 0x17efff75f7f7ff3e 0xffffffffffffffff 0xffffffffffffffff

def z239 : W := mkw 0x282eb1afb41e71f5 0x0505d635f683ce3e 0xa07ff3fff03ff3fe 0xf40ffe7ffe07fe7f

def z240 : W := mkw 0x17d5ef7bc0000000 0x22fabdef78000000 0x03c1ffffc0000004 0x20783ffff8000000

def z241 : W := mkw 0x2000b02d001861a5 0x04001605a0030c34 0xa041f07f003cf3e4 0xf4083e0fe0079e7c

def z242 : W := mkw 0x1ffdef7bc0400600 0x23ffbdef780800c0 0xffffffffc1c01f87 0xfffffffff83803f0

def z243 : W := mkw 0x0000802100c1a6ae 0x00001004201834d5 0xe001806301c7fffc 0xfc00300c6038ffff

def z244 : W := mkw 0x5ff94e50cb600e00 0x2bff29ca196c01c0 0x5fb00c00cfc00c01 0x0bf6018019f80180

def z245 : W := mkw 0x0191846140000000 0x0032308c28000000 0x03b18c63c0000005 0xe076318c78000000

def z246 : W := mkw 0x400000841b281900 0x0800001083650320 0x000000003e380000 0x0000000007c70000

def z247 : W := mkw 0x800210002497c000 0x100042000492f800 0x000000000007e000 0x000000000000fc00

def z248 : W := mkw 0x9b7ff12bedb7c000 0x336ffe257db6f800 0xfffff003ffffe007 0xdffffe007ffffc00

def z249 : W := mkw 0x04040b8292001850 0x008081705240030a 0x0000038000000000 0x0000007000000000

def z250 : W := mkw 0xa006b1af3dbff1e5 0x1400d635e7b7fe3c 0xe04ff3ff3ffff3e6 0xfc09fe7fe7fffe7c

def z251 : W := mkw 0x0191846140c1860a 0x0032308c281830c1 0x43b18c63c1c30c1d 0xe876318c78386183

def z252 : W := mkw 0x0000000000000000 0x0000000000000000 0xa040000030380006 0x9408000006070000

def z253 : W := mkw 0x093de12bc0000000 0x2127bc2578000000 0x007ff3ffc0000006 0xe00ffe7ff8000000

def z254 : W := mkw 0x04848fe3d2403efe 0x009091fc7a4807df 0x00000fe3c0001ff8 0x200001fc780003ff

def z255 : W := mkw 0x1ffdef7bc0818000 0x23ffbdef78103000 0xffffffffc1c7e007 0xfffffffff838fc00

def z256 : W := mkw 0x9b7940000da38000 0x136f280001b47000 0x5ffff0000fc30007 0xcbfffe0001f86000

def z257 : W := mkw 0x09bde56bc0c1a6ae 0x2137bcad781834d5 0xe3bffc63c1c7fffd 0xfc77ff8c7838ffff

def z258 : W := mkw 0x0c2e0b02a6060850 0x0185c16054c0c10a 0x5c3e0c03ce070c79 0x4b87c18079c0e18f

def z259 : W := mkw 0x04800ec012401e00 0x009001d8024803c0 0xff800fe03fc01f87 0xbff001fc07f803f0

def z260 : W := mkw 0x1eec6f5a80000000 0x23dd8deb50000000 0x1fce7ffc00000007 0xa3f9cfff80000000

def z261 : W := mkw 0x2c2e1b86b61e79f5 0x0585c370d6c3cf3e 0xfc3e0f83fe3ffffb 0xff87c1f07fc7ffff

def z262 : W := mkw 0x44800ed41b681f00 0x089001da836d03e0 0xe0000ffc3ff81f80 0x3c0001ff87ff03f0

def z263 : W := mkw 0x89bbd46164d7e6ae 0x11377a8c2c9afcd5 0xe3bffc63c1c7fffd 0xfc77ff8c7838ffff

def z264 : W := mkw 0x52c0045009600600 0x0a58008a012c00c0 0x0380000001c00000 0x0070000000380000

def z265 : W := mkw 0x0006010220040040 0x0000c02044008008 0x000e000300040060 0x4001c0006000800c

def z266 : W := mkw 0x1ffdeffbd2001850 0x23ffbdff7a40030a 0x1fffffffc0001c7f 0xe3fffffff800038f

def z267 : W := mkw 0x00000000000020a4 0x0000000000000414 0xa00000000004f3e0 0x1400000000009e7c

def z268 : W := mkw 0x0000000000000000 0x0000000000000000 0xe380000001c00005 0x9c70000000380000

def z269 : W := mkw 0x811150000091c000 0x10222a0000123800 0x0001f0000000e000 0x00003e0000001c00

def z270 : W := mkw 0x0002100020144000 0x0000420004028800 0xa0000000303ce000 0x1400000006079c00

def z271 : W := mkw 0xc00210843fffdf00 0x1800421087fffbe0 0xe00000003fffff80 0x1c00000007fffff0

def z272 : W := mkw 0x0080044000400600 0x00100088000800c0 0x43800c0001c00c01 0x0870018000380180

def z273 : W := mkw 0x56c00ed01b601e00 0x0ad801da036c03c0 0xdf800f803fc01c03 0xbbf001f007f80380

def z274 : W := mkw 0x1bfde57bc0000000 0x237fbcaf78000000 0x03fff07fc0000004 0x407ffe0ff8000000

def z275 : W := mkw 0x0006118230145040 0x0000c23046028a08 0xa04ff383303cf066 0xf409fe7066079e0c

def z276 : W := mkw 0x0000000000000000 0x0000000000000000 0x40300c00c0030c19 0x0806018018006183

def z277 : W := mkw 0x5eec0fd69b681f00 0x0bdd81fad36d03e0 0xfffe0ffffff81f87 0xffffc1ffffff03f0

def z278 : W := mkw 0x2406bbaf321c79e5 0x0480d775e6438f3c 0xfc4fffff3e3cffe7 0xff89ffffe7c79ffc

def z279 : W := mkw 0x9ffdff7bc9b1c000 0x33ffbfef79363800 0x3fffffffc1f8e007 0xe7fffffff83f1c00

def z280 : W := mkw 0x00008021000020a4 0x0000100420000414 0x200180600000e384 0x0400300c00001c70

def z281 : W := mkw 0x3e6efbbfb01c71e5 0x27cddf77f6038e3c 0xbc4ff3ff303cf3e6 0xf789fe7fe6079e7c

def z282 : W := mkw 0x0004a12b00000000 0x0000942560000000 0x000ff00300000000 0x4001fe0060000000

def z283 : W := mkw 0x0191044040c1860a 0x00322088081830c1 0xe3b00c60c1c31f9d 0xbc76018c183863f3

def z284 : W := mkw 0x011180214081a0ae 0x0022300428103415 0xe3b18003c1c7e07d 0xdc7630007838fc0f

def z285 : W := mkw 0x9b7b50002db7c000 0x136f6a0005b6f800 0xfffffc03fffffc7f 0xffffff807fffff8f

def z286 : W := mkw 0x0191846140000000 0x0032308c28000000 0xc3b18c63c0071c7d 0xf876318c7800e38f

def z287 : W := mkw 0x0195a56b40c1a6ae 0x0032b4ad681834d5 0xe3ffffffc1c7ffff 0xfc7ffffff838ffff

def z288 : W := mkw 0x2006b1af301c71e5 0x0400d635e6038e3c 0xa00ff003303cf3e0 0x5401fe0066079e7c

def z289 : W := mkw 0x16c00e5000400600 0x02d801ca000800c0 0xffc00ffc01c01f87 0xbff801ff803803f0

def z290 : W := mkw 0x01918461400020a4 0x0032308c28000414 0xa3b18c63c004f3e5 0xf476318c78009e7c

def z291 : W := mkw 0x2006a1af300c31e5 0x0400d435e601863c 0x800e03ff300413e2 0xf001c07fe600827c

def z292 : W := mkw 0x0d3febabf6061850 0x21a7fd757ec0c30a 0xdc3fff83fe071c7b 0xfb87fff07fc0e38f

def z293 : W := mkw 0x1ff94e50c0000000 0x23ff29ca18000000 0x1ff00ffcc0000007 0xa3fe01ff98000000

def z294 : W := mkw 0x9a6a50002d364000 0x134d4a0005a6c800 0xdc7e70003e3f0003 0xdb8fce0007c7e000

def z295 : W := mkw 0x04000a0000000000 0x0080014000000000 0x1c000f8000000003 0xa38001f000000000

def z296 : W := mkw 0xbbfff5ef7dfff7ef 0x177ffebdefbffefd 0xffffffffffffffff 0xffffffffffffffff

def z297 : W := mkw 0x0006018230041040 0x0000c03046008208 0x000e038030000002 0x0001c07006000000

def z298 : W := mkw 0x2197b5ef701c71e5 0x0432f6bdee038e3c 0xa3fffffff03cf3e7 0xf47ffffffe079e7c

def z299 : W := mkw 0x16c4af7b00000000 0x02d895ef60000000 0x1fcfffff00000007 0xe3f9ffffe0000000

def z300 : W := mkw 0x52c0045409680700 0x0a58008a812d00e0 0xe3c00c7c01f81f85 0xbc78018f803f03f0

def z301 : W := mkw 0x16400a1000000000 0x02c8014200000000 0x1c40039c00000002 0x0388007380000000

def z302 : W := mkw 0x1ffd6f5ac0000000 0x23ffadeb58000000 0x1ffe7f9cc0000003 0x03ffcff398000000

def z303 : W := mkw 0x2117b1af709df1ef 0x0422f635ee13be3d 0xa07ff3fff03ff3fe 0xf40ffe7ffe07fe7f

def z304 : W := mkw 0x0004a12b00000000 0x0000942560000000 0x000003ff00000000 0x2000007fe0000000

def z305 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000c03c0001c78 0x200001807800038f

def z306 : W := mkw 0x0dbf0fc2f6c79e5a 0x01b7e1f85ed8f3cb 0xdfbe0f83ffc71c7b 0xfbf7c1f07ff8e38f

def z307 : W := mkw 0x9b7b40002da78000 0x136f680005b4f000 0xdfbe00003fc70003 0xdbf7c00007f8e000

def z308 : W := mkw 0x56c00ed41b681f00 0x0ad801da836d03e0 0x5fc00f9c3ff80c03 0x0bf801f387ff0180

def z309 : W := mkw 0x0111e02940000000 0x20223c0528000000 0x0001f00000000000 0x00003e0000000000

def z310 : W := mkw 0x1fffeffbf0041040 0x23fffdff7e008208 0x9ffffffff0041067 0xf3fffffffe00820c

def z311 : W := mkw 0x52c0045409680700 0x0a58008a812d00e0 0xffc0007c3ff80387 0x9ff8000f87ff0070

def z312 : W := mkw 0x1ffdef7bc0000000 0x23ffbdef78000000 0xdfffffffc0071c7f 0xfbfffffff800e38f

def z313 : W := mkw 0x56c00e500b600e00 0x0ad801ca016c01c0 0xffc00c003ff80c07 0x9ff8018007ff0180

def z314 : W := mkw 0x56400a941b281900 0x0ac8015283650320 0xbc4003fc3e381386 0xb788007f87c70270

def z315 : W := mkw 0x400000841be9bfae 0x08000010837d37f5 0xe00000003ffffff8 0x1c00000007ffffff

def z316 : W := mkw 0x2004b12f001861a5 0x04009625e0030c34 0x204ff3ff0038e386 0xe409fe7fe0071c70

def z317 : W := mkw 0x2191b46d40d9e7af 0x0432368da81b3cf5 0xe3f1fc7fc1fffffd 0xfc7e3f8ff83fffff

def z318 : W := mkw 0x56c00e500b600e00 0x0ad801ca016c01c0 0x5fc00ffc0fc00c07 0xabf801ff81f80180

def z319 : W := mkw 0x1eee0fd2b6061850 0x03ddc1fa56c0c30a 0xdffe0ffffe071c7f 0xfbffc1ffffc0e38f

def z320 : W := mkw 0xa00210843dbff1e5 0x1400421087b7fe3c 0xe00000003ffff3e0 0x1c00000007fffe7c

def z321 : W := mkw 0x200290a5301c71e5 0x04005214a6038e3c 0xa0018063303cf3e4 0xf400300c66079e7c

def z322 : W := mkw 0x811310002db7c000 0x1022620005b6f800 0xe3b180003fffe005 0xdc76300007fffc00

def z323 : W := mkw 0x52c004d41b681f00 0x0a58009a836d03e0 0xe3c0007c3ff81f84 0x1c78000f87ff03f0

def z324 : W := mkw 0x011180210081a0a4 0x0022300420103414 0xe3b1806301c7f3e5 0xfc76300c6038fe7c

def z325 : W := mkw 0x0484af7bc0000000 0x209095ef78000000 0x004fffffc0000006 0xe009fffff8000000

def z326 : W := mkw 0x1bf9c46140000000 0x037f388c28000000 0x1ffffc63c0000007 0xe3ffff8c78000000

def z327 : W := mkw 0x1ffdef7bc04026ae 0x23ffbdef780804d5 0x1fffffffc0001fff 0xe3fffffff80003ff

def z328 : W := mkw 0x44000a841b681f00 0x08800150836d03e0 0xfc000f803ff81f83 0xbf8001f007ff03f0

def z329 : W := mkw 0x6484afff12483fe5 0x0c9095ffe24907fc 0x00000fff00001fe0 0x200001ffe00003fc

def z330 : W := mkw 0x0004018210001040 0x0000803042000208 0x0000038300001060 0x200000706000020c

def z331 : W := mkw 0x893ff12be497c000 0x3127fe257c92f800 0x003ff003c007e000 0x4007fe007800fc00

def z332 : W := mkw 0x1b7de12bc0000000 0x236fbc2578000000 0x1ffff003c0000007 0xc3fffe0078000000

def z333 : W := mkw 0x9b7b50803fb7d850 0x136f6a1007f6fb0a 0xfffff0003ffffc7f 0xdffffe0007ffff8f

def z334 : W := mkw 0x1ffdef7bc081a0ae 0x23ffbdef78103415 0x1fffffffc007e07f 0xe3fffffff800fc0f

def z335 : W := mkw 0x04000a0002000800 0x0080014000400100 0x5c000c000e000c01 0x0b80018001c00180

def z336 : W := mkw 0x1ffdef7bc6020810 0x23ffbdef78c04102 0x5fffffffce030c1f 0xebfffffff9c06183

def z337 : W := mkw 0x0002008036061850 0x0000401006c0c30a 0xc0300c03fe071c79 0xf80601807fc0e38f

def z338 : W := mkw 0x53d1847549e9a7ae 0x0a7a308ea93d34f5 0x23c1807c01f8e384 0x0478300f803f1c70

def z339 : W := mkw 0x8939400004838000 0x1127280000907000 0x0030000000030000 0x0006000000006000

def z340 : W := mkw 0x5ffdef7bcb600e00 0x2bffbdef796c01c0 0x5fffffffcfc00c07 0xebfffffff9f80180

def z341 : W := mkw 0xbb7bf02d2dbfe1a5 0x176f7e05a5b7fc34 0xfffff07c3fffe387 0xdffffe0f87fffc70

def z342 : W := mkw 0x2486bffff01c71e5 0x2490d7fffe038e3c 0xa04ffffff03cf3e6 0xf409fffffe079e7c

def z343 : W := mkw 0x9fffff7bedf7e6ae 0x33ffffef7dbefcd5 0xffffffffffffffff 0xffffffffffffffff

def z344 : W := mkw 0x93d1d46149f1e6ae 0x127a3a8c293e3cd5 0x23c1f06001f8e384 0x04783e0c003f1c70

def z345 : W := mkw 0x0000a02900000000 0x0000140520000000 0x0041f07c00000004 0x00083e0f80000000

def z346 : W := mkw 0x2004218e10081141 0x04008431c2010228 0x0000039c00000000 0x0000007380000000

def z347 : W := mkw 0x04000a8012001800 0x0080015002400300 0xdc300f83fe071c7b 0xfb8601f07fc0e38f

def z348 : W := mkw 0x04800e5000000000 0x009001ca00000000 0x00000ffc00000000 0x200001ff80000000

def z349 : W := mkw 0x04060b8232041840 0x0080c17046408308 0xdc0e0f833e041c63 0xfb81c1f067c0838c

def z350 : W := mkw 0x019184e550c9b7ae 0x0032309caa1936f5 0xe3f18ffff1ffffff 0xfc7e31fffe3fffff

def z351 : W := mkw 0x5ee80ed49f6a1f10 0x0bdd01da93ed43e2 0xfff00ffcfffb1f9f 0xbffe01ff9fff63f3

def z352 : W := mkw 0x16c00e5000000000 0x02d801ca00000000 0x1f800c0000000001 0x03f0018000000000

def z353 : W := mkw 0x082a000024060000 0x010540000480c000 0xdc3e0c03fe071c7b 0xfb87c1807fc0e38f

def z354 : W := mkw 0x9fffff7bed364000 0x33ffffef7da6c800 0x1ffffffffe380007 0xe3ffffffffc70000

def z355 : W := mkw 0x093fe12be4060050 0x2127fc257c80c00a 0x003ff003c0070078 0x4007fe007800e00f

def z356 : W := mkw 0x0080044000c1a6ae 0x00100088001834d5 0xe3800c6001c7fffd 0xbc70018c0038ffff

def z357 : W := mkw 0x0dbd8f63c0000000 0x01b7b1ec78000000 0x1fbf8fe3c0000007 0xe3f7f1fc78000000

def z358 : W := mkw 0x0191846140c1a6ae 0x0032308c281834d5 0x23b18063c1c7e3fc 0x4476300c7838fc7f

def z359 : W := mkw 0x1b7de12b00000000 0x036fbc2560000000 0x1ffff3ff00000007 0xe3fffe7fe0000000

def z360 : W := mkw 0x9b7b50002db7c000 0x136f6a0005b6f800 0x3fcff0003ff8e006 0x07f9fe0007ff1c00

def z361 : W := mkw 0x0191846140c1a6ae 0x0032308c281834d5 0xe3818c6001c0ff85 0xbc70318c00381ff0

def z362 : W := mkw 0x8000100009b1c000 0x1000020001363800 0x2000000001f8e000 0x04000000003f1c00

def z363 : W := mkw 0xbb7ff12b2db7e0e5 0x176ffe2565b6fc1c 0xfffff0033fffe067 0xdffffe0067fffc0c

def z364 : W := mkw 0x0c2c0b8296021850 0x0185817052c0430a 0x5c300f83ce031c79 0x2b8601f079c0638f

def z365 : W := mkw 0x1fffeffbf6061850 0x23fffdff7ec0c30a 0x1ffffffffe000007 0xe3ffffffffc00000

def z366 : W := mkw 0x1a6a00002d260000 0x034d400005a4c000 0xfffe00003fff0007 0xdfffc00007ffe000

def z367 : W := mkw 0x008004404040060a 0x00100088080800c1 0x00000c00c0000c18 0x0000018018000183

def z368 : W := mkw 0x2004b1af101871e5 0x04009635e2030e3c 0x2041f3ff0038f3e4 0x24083e7fe0071e7c

def z369 : W := mkw 0xa93ff12b2497e0e5 0x1527fe256492fc1c 0x003ff0030007e060 0x4007fe006000fc0c

def z370 : W := mkw 0x5eec6fde9b681f00 0x2bdd8dfbd36d03e0 0xffce7ffc3ff81f87 0xbff9cfff87ff03f0

def z371 : W := mkw 0x082c010280000000 0x0105802050000000 0x003e0003c0000000 0x4007c00078000000

def z372 : W := mkw 0x0002100020144000 0x0000420004028800 0x004e700030380002 0x0009ce0006070000

def z373 : W := mkw 0x1ff9ee79c0000000 0x23ff3dcf38000000 0x1ff1fc7cc0000005 0x03fe3f8f98000000

def z374 : W := mkw 0x0000008410081100 0x0000001082010220 0x000003fc00001380 0x2000007f80000270

def z375 : W := mkw 0x33d1f47d401861a5 0x267a3e8fa8030c34 0x23c1f07c0038e384 0x04783e0f80071c70

def z376 : W := mkw 0x524000841b681f00 0x0a480010836d03e0 0xffc000003ff81f87 0x9ff8000007ff03f0

def z377 : W := mkw 0x0191846140c1a6ae 0x0032308c281834d5 0xe3b1806001c7e385 0xdc76300c0038fc70

def z378 : W := mkw 0x44800e5002400e00 0x089001ca004801c0 0x00000c0000000c00 0x0000018000000180

def z379 : W := mkw 0x0c2a0a00a6060810 0x0185414014c0c102 0xdc3e0c00fe070c1b 0xdb87c1801fc0e183

def z380 : W := mkw 0x5e6e0b96bf2e1950 0x0bcdc172d7e5c32a 0x1c4e039c3e380002 0x0389c07387c70000

def z381 : W := mkw 0x56c08ef51b683fa4 0x0ad811dea36d07f4 0xffc18fff3ffcffe7 0xfff831ffe7ff9ffc

def z382 : W := mkw 0x2195a5ef50c9b7ef 0x0432b4bdea1936fd 0xe3b18fffc1c7fffd 0xfc7631fff838ffff

def z383 : W := mkw 0x57d18ef55b681f00 0x0afa31deab6d03e0 0xfff18ffffff81f87 0xfffe31ffffff03f0

def z384 : W := mkw 0x00808461404026ae 0x0010108c280804d5 0xe3800c63c1c01ffd 0xbc70018c783803ff

def z385 : W := mkw 0x56400a941b281900 0x0ac8015283650320 0xdc400f9c3e381c03 0xbb8801f387c70380

def z386 : W := mkw 0x0004010280000050 0x000080205000000a 0x00000003c0000078 0x000000007800000f

def z387 : W := mkw 0x282eb1af341e71e5 0x0505d635e683ce3c 0xfc7ff3ff3e3ff3e7 0xff8ffe7fe7c7fe7c

def z388 : W := mkw 0x1f7d4b0280000000 0x03efa96050000000 0x1fffff83c0000007 0xe3fffff078000000

def z389 : W := mkw 0x9ffb5e502db7c000 0x13ff6bca05b6f800 0xfffffffc3fffe007 0xffffffff87fffc00

def z390 : W := mkw 0x1e6e6b9ab6061850 0x23cdcd7356c0c30a 0x1c4e739c3e000002 0x0389ce7387c00000

def z391 : W := mkw 0x400200843f6e1f50 0x0800401087edc3ea 0xe00000003fff1ff8 0x1c00000007ffe3ff

def z392 : W := mkw 0x1b79400009200000 0x036f280001240000 0xfffff0003ff80007 0xdffffe0007ff0000

def z393 : W := mkw 0x600210843b7c7fe5 0x0c004210876f8ffc 0xe00000003ffcffe0 0x1c00000007ff9ffc

def z394 : W := mkw 0xd3d1545409f9c700 0x1a7a2a8a813f38e0 0x23c1f07c01f8e384 0x04783e0f803f1c70

def z395 : W := mkw 0x5ffdefffd2481f00 0x2bffbdfffa4903e0 0x1fffffffc0001f87 0xe3fffffff80003f0

def z396 : W := mkw 0x2086b5ef305c77e5 0x0410d6bde60b8efc 0xe3cfffff31fcffe7 0xfc79ffffe63f9ffc

def z397 : W := mkw 0x0caeaffbf6061850 0x2195d5ff7ec0c30a 0xdc3e0ffffe071c7b 0xfb87c1ffffc0e38f

def z398 : W := mkw 0x0000000000c1860a 0x00000000001830c1 0x4000000001c30c18 0x0800000000386183

def z399 : W := mkw 0x0000000000c1a6ae 0x00000000001834d5 0x2000000001c0e380 0x0400000000381c70

def z400 : W := mkw 0x2006b1af30ddf7ef 0x0400d635e61bbefd 0xe04ff3ff31fffffe 0xfc09fe7fe63fffff

def z401 : W := mkw 0x0000000000000000 0x0000000000000000 0xa000006000001384 0xb400000c00000270

def z402 : W := mkw 0x0080044000400600 0x00100088000800c0 0x00000c6000001f80 0x2000018c000003f0

def z403 : W := mkw 0x0000000000c1a6ae 0x00000000001834d5 0xe0300c03c1c7fff9 0xfc0601807838ffff

def z404 : W := mkw 0x0191044040c1860a 0x00322088081830c1 0xc3b00c03c1c71c79 0xf87601807838e38f

def z405 : W := mkw 0x219394e570ddf7ef 0x0432729cae1bbefd 0xe3b18c63f1fffffd 0xfc76318c7e3fffff

def z406 : W := mkw 0x0191846140c1a6ae 0x0032308c281834d5 0xa381806301c4f3e4 0xf470300c60389e7c

def z407 : W := mkw 0x3ffdff7fc01861a5 0x27ffbfeff8030c34 0x3fffffffc038e387 0xe7fffffff8071c70

def z408 : W := mkw 0x011180214081a0ae 0x0022300428103415 0xa0318063c007f3fc 0xf406300c7800fe7f

def z409 : W := mkw 0x05918ee152c1beae 0x00b231dc2a5837d5 0xffb18fe3ffc7ffff 0xfff631fc7ff8ffff

def z410 : W := mkw 0x17d18e7140000000 0x02fa31ce28000000 0x1ff18fffc0000007 0xe3fe31fff8000000

def z411 : W := mkw 0x1fffef7be4060000 0x23fffdef7c80c000 0xdffffffffe070007 0xfbffffffffc0e000

def z412 : W := mkw 0xba6e718e3d3e5141 0x174dce31c7a7ca28 0x1c4e739c3e380002 0x0389ce7387c70000

def z413 : W := mkw 0x56c00ed41be9bfae 0x0ad801da837d37f5 0xffc00ffc3fffffff 0xbff801ff87ffffff

def z414 : W := mkw 0xbb7f718e3dbfd141 0x176fee31c7b7fa28 0xfffff39c3fffe007 0xdffffe7387fffc00

def z415 : W := mkw 0x0000000000000000 0x0000000000000000 0xdc0000003e000003 0x9b80000007c00000

def z416 : W := mkw 0x16c00ed410081100 0x02d801da82010220 0xbfc00ffc30381387 0xb7f801ff86070270

def z417 : W := mkw 0x400000000b600e00 0x08000000016c01c0 0x400000000fc00c00 0x0800000001f80180

def z418 : W := mkw 0x5fff8ff7ffefbffe 0x0bfff1fefffdf7ff 0xffff8fffffffffff 0xfffff1ffffffffff

def z419 : W := mkw 0x57d10ed45be99f0a 0x0afa21da8b7d33e1 0xfff00ffcfffb1f9f 0xbffe01ff9fff63f3

def z420 : W := mkw 0x53d1e47d49680700 0x2a7a3c8fa92d00e0 0x23c1f07c01f80384 0x04783e0f803f0070

def z421 : W := mkw 0x1ffdef7bc0c1860a 0x23ffbdef781830c1 0x5fffffffc1c30c1f 0xebfffffff8386183

def z422 : W := mkw 0x1bf9c46140c1a6ae 0x037f388c281834d5 0xfffffc63c1c7ffff 0xffffff8c7838ffff

def z423 : W := mkw 0x2c2ebbafb61e79f5 0x0585d775f6c3cf3e 0xbc4ff3ff3e3cf3e6 0xf789fe7fe7c79e7c

def z424 : W := mkw 0x9b7b50002d364000 0x136f6a0005a6c800 0x1ffff0003e380007 0xc3fffe0007c70000

def z425 : W := mkw 0x0002000024060000 0x000040000480c000 0xc00000003e070000 0x1800000007c0e000

def z426 : W := mkw 0x56c60fd63b6c1f40 0x0ad8c1fac76d83e8 0xffce0fff3ffc1fe7 0xfff9c1ffe7ff83fc

def z427 : W := mkw 0x16400a801b201800 0x02c8015003640300 0xffc00f803ff81c07 0xbff801f007ff0380

def z428 : W := mkw 0x4c2e0b86bf6e1f50 0x0985c170d7edc3ea 0xfc3e0f83ffff1ffb 0xff87c1f07fffe3ff

def z429 : W := mkw 0x0c2c0b8292001850 0x018581705240030a 0x1c3e0f83c0001c7b 0xe387c1f07800038f

def z430 : W := mkw 0x8c2e1b82bfb7d850 0x1185c37057f6fb0a 0xfc3e0f83fffffc7b 0xff87c1f07fffff8f

def z431 : W := mkw 0x1e6e6b9ab6061850 0x23cdcd7356c0c30a 0xdc7e7f9ffe071c7b 0xfb8fcff3ffc0e38f

def z432 : W := mkw 0x0191846140000000 0x0032308c28000000 0x0381806000000004 0x0070300c00000000

def z433 : W := mkw 0x0191044040000000 0x0032208808000000 0x03b00c00c0000001 0x0076018018000000

def z434 : W := mkw 0x9bfb54402df7c600 0x137f6a8805bef8c0 0xfffffc603fffff87 0xffffff8c07fffff0

def z435 : W := mkw 0x05958fe3d2c1befe 0x00b2b1fc7a5837df 0xe3b18fe3c1c7fffd 0xfc7631fc7838ffff

def z436 : W := mkw 0x893b50002497c000 0x11276a000492f800 0xe3bff00001c7e005 0xdc77fe000038fc00

def z437 : W := mkw 0x0191846140c1a6ae 0x0032308c281834d5 0x43b18c03c1c7ec79 0x487631807838fd8f

def z438 : W := mkw 0x0000802100000000 0x0000100420000000 0x0001806300000004 0xe000300c60000000

def z439 : W := mkw 0x0004010200000000 0x0000802040000000 0x000e038300000002 0xe001c07060000000

def z440 : W := mkw 0x13d5e57b40000000 0x227abcaf68000000 0x03cff3ff00000006 0xe079fe7fe0000000

def z441 : W := mkw 0x1b7b500020144000 0x036f6a0004028800 0xbffff000303ce007 0xd7fffe0006079c00

def z442 : W := mkw 0x0c2c0b8292001800 0x0185817052400300 0xdc3e0f83fe001c03 0xfb87c1f07fc00380

def z443 : W := mkw 0xdb7b50843fffdf00 0x1b6f6a1087fffbe0 0xfffff0003fffff87 0xdffffe0007fffff0

def z444 : W := mkw 0x0c2e0b82b6061850 0x0185c17056c0c30a 0x003e0f83c0071c78 0x6007c1f07800e38f

def z445 : W := mkw 0x2006b1af301c71e5 0x0400d635e6038e3c 0x204ff3fc3038e386 0x0409fe7f86071c70

def z446 : W := mkw 0x0c2c0b0280000000 0x0185816050000000 0xdc3e0f83c0071c7b 0xfb87c1f07800e38f

def z447 : W := mkw 0x72c6b5ff397c77e5 0x0e58d6bfe72f8efc 0xa3cff3ff31fcf3e6 0xf479fe7fe63f9e7c

def z448 : W := mkw 0x4000008412481f00 0x08000010824903e0 0x0000000000001f80 0x00000000000003f0

def z449 : W := mkw 0x0111000000818000 0x0022200000103000 0x003180000007e000 0x400630000000fc00

def z450 : W := mkw 0x9e6e5b82bf365850 0x13cdcb7057e6cb0a 0xdc7e7f83fe3f1c7b 0xfb8fcff07fc7e38f

def z451 : W := mkw 0x293ff1aff01c71e5 0x2527fe35fe038e3c 0xa07ff3fff03cf3e6 0xf40ffe7ffe079e7c

def z452 : W := mkw 0x2404abaf920839f5 0x04809575f241073e 0x00000fffc0001ff8 0x200001fff80003ff

def z453 : W := mkw 0x2004a12b000020e5 0x040094256000041c 0x0000000300000060 0x000000006000000c

def z454 : W := mkw 0x1ffdef7bc00020a4 0x23ffbdef78000414 0xbfffffffc004f3e7 0xf7fffffff8009e7c

def z455 : W := mkw 0x1e6ceb3b80000000 0x23cd9d6770000000 0x1c4ff3ff00000006 0xe389fe7fe0000000

def z456 : W := mkw 0x0dbd8f63c0c1a6ae 0x01b7b1ec781834d5 0xffbf8fe3c1c7ffff 0xfff7f1fc7838ffff

def z457 : W := mkw 0x9f7f5b02adb7c000 0x13efeb6055b6f800 0xffffff83ffffe007 0xfffffff07ffffc00

def z458 : W := mkw 0x1351400000000000 0x026a280000000000 0x03c1f00000000004 0x00783e0000000000

def z459 : W := mkw 0x9e6e7b1aad364000 0x33cdcf6355a6c800 0x1c4e739c3e380002 0x0389ce7387c70000

def z460 : W := mkw 0x5ff94ed4db681f00 0x2bff29da9b6d03e0 0xfff00ffcfff81f87 0xbffe01ff9fff03f0

def z461 : W := mkw 0x04042b1a80000000 0x2080856350000000 0x0000039c00000000 0x0000007380000000

def z462 : W := mkw 0x0080a47940000000 0x2010148f28000000 0x0000007c00000000 0x0000000f80000000

def z463 : W := mkw 0x0db90e40c6c38e1a 0x01b721c818d871c3 0x5fb00c00cfc30c19 0x0bf6018019f86183

def z464 : W := mkw 0x0111000000818000 0x0022200000103000 0x43b0000001c30001 0x0876000000386000

def z465 : W := mkw 0x0000008012001850 0x000000100240030a 0x0000000000001c78 0x000000000000038f

def z466 : W := mkw 0x0828000004020000 0x0105000000804000 0x5c3000000e030001 0x0b86000001c06000

def z467 : W := mkw 0x2000300c00184101 0x0400060180030820 0x0040701c00380000 0x00080e0380070000

def z468 : W := mkw 0x0c2e0b82b6061850 0x0185c17056c0c30a 0x1c0e0f83fe001c7a 0x2381c1f07fc0038f

def z469 : W := mkw 0x893b50002497c000 0x11276a000492f800 0xdc3ff0003e07e003 0xdb87fe0007c0fc00

def z470 : W := mkw 0x5ffdef7fc9680700 0x2bffbdeff92d00e0 0x3fffffffc1f80387 0xe7fffffff83f0070

def z471 : W := mkw 0x1fff4fd2f6061850 0x23ffe9fa5ec0c30a 0xdfbe0f83fe071c7b 0xfbf7c1f07fc0e38f

def z472 : W := mkw 0x019785e370c5b6ee 0x0032f0bc6e18b6dd 0xe3bf8fe3f1c7ffff 0xfc77f1fc7e38ffff

def z473 : W := mkw 0x0d3deb2bc0000000 0x21a7bd6578000000 0x1c3fff83c0000003 0xe387fff078000000

def z474 : W := mkw 0x0006018236061850 0x0000c03046c0c30a 0xc00e03833e071c7a 0xf801c07067c0e38f

def z475 : W := mkw 0x16c00e5009200000 0x02d801ca01240000 0xffc00ffc3ff80007 0xbff801ff87ff0000

def z476 : W := mkw 0x1ffdeffbd2001800 0x23ffbdff7a400300 0xdffffffffe001c07 0xfbffffffffc00380

def z477 : W := mkw 0x6006b1af3b7c7fe5 0x0c00d635e76f8ffc 0xe04ff3ff3ffcffe6 0xfc09fe7fe7ff9ffc

def z478 : W := mkw 0x0000000000000000 0x0000000000000000 0x00300003c0070078 0x400600007800e00f

def z479 : W := mkw 0x082e018234061040 0x0105c0304680c208 0xdc3e03833e071063 0xfb87c07067c0e20c

def z480 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0000c0000001c01 0xb800018000000380

def z481 : W := mkw 0x0484affbd2001850 0x209095ff7a40030a 0x00000fffc0001c78 0x200001fff800038f

def z482 : W := mkw 0x57d1eefd5b681f00 0x2afa3ddfab6d03e0 0xffc1fffc3ff81f87 0xbff83fff87ff03f0

def z483 : W := mkw 0x9a6840000d220000 0x134d080001a44000 0x1c0000000e000000 0x0380000001c00000

def z484 : W := mkw 0x2006b1af301c71e5 0x0400d635e6038e3c 0x004ff39f303ce062 0x4009fe73e6079c0c

def z485 : W := mkw 0x2006b1af301c71e5 0x0400d635e6038e3c 0xa00003ff303cf3e0 0x3400007fe6079e7c

def z486 : W := mkw 0x2004a1af100831e5 0x04009435e201063c 0xa04003ff303813e6 0xb408007fe607027c

def z487 : W := mkw 0x0111802140000000 0x0022300428000000 0x00318003c0000000 0x4006300078000000

def z488 : W := mkw 0x9a6a50002d364000 0x134d4a0005a6c800 0xbc4ff0003e3ce006 0xd789fe0007c79c00

def z489 : W := mkw 0x2002b0ad301c71e5 0x04005615a6038e3c 0xa041f07c303cf3e4 0x14083e0f86079e7c

def z490 : W := mkw 0x0c2e0b82b6061850 0x0185c17056c0c30a 0x1c3e0f83fe000003 0xe387c1f07fc00000

def z491 : W := mkw 0x011180214081a0ae 0x0022300428103415 0xc0318c03c007fc79 0xf80631807800ff8f

def z492 : W := mkw 0x0000000009200000 0x0000000001240000 0xe00000003ff80000 0x1c00000007ff0000

def z493 : W := mkw 0x0c2e8ba3b60638f4 0x0185d17476c0c71e 0xfc3f8fe3fe07ffff 0xff87f1fc7fc0ffff

def z494 : W := mkw 0x56c00ed41b681f00 0x0ad801da836d03e0 0xff800c003ff81f81 0x1ff0018007ff03f0

def z495 : W := mkw 0x2197b56b60d5e6ef 0x0432f6ad6c1abcdd 0xe3bffc63c1c7fffd 0xfc77ff8c7838ffff

def z496 : W := mkw 0x893b50002db7c000 0x11276a0005b6f800 0xe03ff0003fffe000 0x5c07fe0007fffc00

def z497 : W := mkw 0x77d7bfff7bfdffef 0x0efaf7ffef7fbffd 0xffffffffffffffff 0xffffffffffffffff

def z498 : W := mkw 0x0080846140000000 0x0010108c28000000 0x00000c63c0000000 0x2000018c78000000

def z499 : W := mkw 0x893bd0216497e0ae 0x11277a042c92fc15 0x003ff003c007e078 0x4007fe007800fc0f

def z500 : W := mkw 0x04040b8292001850 0x008081705240030a 0xc0300f83c0071c79 0xf80601f07800e38f

def z501 : W := mkw 0x1eec0f5280000000 0x03dd81ea50000000 0x1ffe0fffc0000007 0xe3ffc1fff8000000

def z502 : W := mkw 0x0000000000000000 0x0000000000000000 0xc030000000070001 0xd80600000000e000

def z503 : W := mkw 0x2084a5ef504837ef 0x041094bdea0906fd 0x00000fffc0001ff8 0x200001fff80003ff

def z504 : W := mkw 0x0cae0fc2b6461e50 0x0195c1f856c8c3ca 0xffbe0fe3ffc71fff 0xfff7c1fc7ff8e3ff

def z505 : W := mkw 0x20061186301c71e5 0x0400c230c6038e3c 0xa00e0383303cf3e2 0xf401c07066079e7c

def z506 : W := mkw 0x0002000020040000 0x0000400004008000 0x800e000030040002 0xd001c00006008000

def z507 : W := mkw 0x56c00ed412481f00 0x0ad801da824903e0 0x1fc00ffc00001f87 0xa3f801ff800003f0

def z508 : W := mkw 0x20021084301c71e5 0x0400421086038e3c 0xa04ff000303cf3e6 0xd409fe0006079e7c

def z509 : W := mkw 0x0111000000818000 0x0022200000103000 0xe3b18c03c1c7fc7d 0xfc7631807838ff8f

def z510 : W := mkw 0x0006b12b20144000 0x0000d62564028800 0xa04ff3ff303ce006 0xf409fe7fe6079c00

def z511 : W := mkw 0x893f5102a497c050 0x1127ea205492f80a 0x003ff003c007e078 0x4007fe007800fc0f

def z512 : W := mkw 0x0c2e0b02a4060000 0x0185c1605480c000 0xdc3e0f83fe070003 0xfb87c1f07fc0e000

def z513 : W := mkw 0x72c0b47d097867a5 0x0e58168fa12f0cf4 0x23c1f07c01f8e384 0x04783e0f803f1c70

def z514 : W := mkw 0x4484afffd2481f00 0x289095fffa4903e0 0x00000fffc0001f80 0x200001fff80003f0

def z515 : W := mkw 0x0c2e0b82b6061850 0x0185c17056c0c30a 0xdc0e0f803e001c03 0xbb81c1f007c00380

def z516 : W := mkw 0x17d18e7140c1a6ae 0x02fa31ce281834d5 0xfff18fffc1c7ffff 0xfffe31fff838ffff

def z517 : W := mkw 0x282eb12ba41660f5 0x0505d6257482cc1e 0x003ff003c007e078 0x4007fe007800fc0f

def z518 : W := mkw 0x2000b029001060a5 0x0400160520020c14 0x0001f0000000e000 0x00003e0000001c00

def z519 : W := mkw 0x1e6e0b82bf261850 0x03cdc17057e4c30a 0xfffe0f83ffff1c7f 0xffffc1f07fffe38f

def z520 : W := mkw 0x0c280a0080000000 0x0185014010000000 0x1c300c00c0000001 0x0386018018000000

def z521 : W := mkw 0x2002b02d201c61a5 0x04005605a4038c34 0xa04ff07c303ce386 0xd409fe0f86079c70

def z522 : W := mkw 0x9b7ff12b2db7c000 0x136ffe2565b6f800 0xfffff3ff3fffe007 0xfffffe7fe7fffc00

def z523 : W := mkw 0x9ffdef7bcda38000 0x33ffbdef79b47000 0x5fffffffcfc30007 0xebfffffff9f86000

def z524 : W := mkw 0x04040b8292001850 0x008081705240030a 0xdc000f83fe001c7b 0xbb8001f07fc0038f

def z525 : W := mkw 0x2006b12b201460e5 0x0400d62564028c1c 0xa00ff0630004f3e4 0xf401fe0c60009e7c

def z526 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000000300041060 0xf00000006000820c

def z527 : W := mkw 0x1ffdef7bc0000000 0x23ffbdef78000000 0x1fb00fffc0000001 0x23f601fff8000000

def z528 : W := mkw 0x0000000000818000 0x0000000000103000 0xe000000001c7e000 0x1c0000000038fc00

def z529 : W := mkw 0x082c610a80000000 0x21058c2150000000 0x000e700000000000 0x0001ce0000000000

def z530 : W := mkw 0x56c00e540b680f00 0x0ad801ca816d01e0 0x7fc00c7c0ff80f85 0x0ff8018f81ff01f0

def z531 : W := mkw 0x00060186300c1140 0x0000c030c6018228 0xa04e03ff303c13e6 0xf409c07fe607827c

def z532 : W := mkw 0x9e6e5b82bf365850 0x13cdcb7057e6cb0a 0x1c4e73803e380002 0x0389ce7007c70000

def z533 : W := mkw 0x9240500009304000 0x12480a0001260800 0x0040700000380000 0x00080e0000070000

def z534 : W := mkw 0x0828000000000000 0x0105000000000000 0x1c3e000000000003 0xc387c00000000000

def z535 : W := mkw 0xd7d15ed41bf9df00 0x1afa2bda837f3be0 0xffc1fffc3ff8ff87 0xbff83fff87ff1ff0

def z536 : W := mkw 0x0c2e0b82b0041040 0x0185c17056008208 0x9c3e0f83f0041063 0xf387c1f07e00820c

def z537 : W := mkw 0x800000000da38000 0x1000000001b47000 0x400000000fc30000 0x0800000001f86000

def z538 : W := mkw 0x0c280a0086020810 0x0185014010c04102 0x1c0000000e000000 0x0380000001c00000

def z539 : W := mkw 0x1ff9ce71c0000000 0x23ff39ce38000000 0x1fb18c63c0000005 0xe3f6318c78000000

def z540 : W := mkw 0x2006b1af301c71e5 0x0400d635e6038e3c 0x004e73ff303813e2 0x2009ce7fe607027c

def z541 : W := mkw 0x4080045400480700 0x0810008a800900e0 0x0000007c00000380 0x0000000f80000070

def z542 : W := mkw 0x800210002db7c000 0x1000420005b6f800 0xe04ff0003fffe006 0xdc09fe0007fffc00

def z543 : W := mkw 0x7ffffffffb7c7fe5 0x2fffffffff6f8ffc 0xfffffffffffcffe7 0xffffffffffff9ffc

def z544 : W := mkw 0x9b7bd0212db7e0a4 0x136f7a0425b6fc14 0xfffff0633ffff3e7 0xfffffe0c67fffe7c

def z545 : W := mkw 0x008004c410481700 0x00100098820902e0 0xe3c00ffc31f81f87 0xbc7801ff863f03f0

def z546 : W := mkw 0x0193946160d5e6ae 0x0032728c2c1abcd5 0xe3fffc63f1ffffff 0xfc7fff8c7e3fffff

def z547 : W := mkw 0x1fffff7be0144000 0x23ffffef7c028800 0xbffffffff03ce007 0xf7fffffffe079c00

def z548 : W := mkw 0x04060b82b6061850 0x0080c17056c0c30a 0xc0000f83fe071c78 0x380001f07fc0e38f

def z549 : W := mkw 0x1240601800000000 0x22480c0300000000 0x0040701c00000000 0x00080e0380000000

def z550 : W := mkw 0x1ff94e50c6020810 0x23ff29ca18c04102 0x5fb00c00ce030c19 0x0bf6018019c06183

def z551 : W := mkw 0x0004a1af10081100 0x00009435e2010220 0xa04ff3ff30381386 0xf409fe7fe6070270

def z552 : W := mkw 0x0c2e0b82b6061850 0x0185c17056c0c30a 0x9c0e03833e041062 0xf381c07067c0820c

def z553 : W := mkw 0x9353500029b5c000 0x126a6a000536b800 0xa3cff00031fce006 0xd479fe00063f9c00

def z554 : W := mkw 0x44800ed412481f00 0x089001da824903e0 0xdc000ffc3e001f83 0xbb8001ff87c003f0

def z555 : W := mkw 0x5ffdefffdb281900 0x2bffbdfffb650320 0x1ffffffffe380007 0xe3ffffffffc70000

def z556 : W := mkw 0x082a000024060000 0x010540000480c000 0x003e000000070000 0x4007c0000000e000

def z557 : W := mkw 0x0d3f0b82b6879850 0x01a7e17056d0f30a 0xffbf8f83ffc7fc7f 0xfff7f1f07ff8ff8f

def z558 : W := mkw 0x0004a12bc0000000 0x2000942578000000 0x00000003c0000000 0x0000000078000000

def z559 : W := mkw 0x0191044040c1860a 0x00322088081830c1 0x0380000001c00000 0x0070000000380000

def z560 : W := mkw 0x0c2e0b82b6061850 0x0185c17056c0c30a 0x5c3e0f80fe030c1b 0x0b87c1f01fc06183

def z561 : W := mkw 0x0000008010001000 0x0000001002000200 0x8000038030001002 0xb000007006000200

def z562 : W := mkw 0x16c4af7bc0000000 0x22d895ef78000000 0x1fc00fffc0000007 0xa3f801fff8000000

def z563 : W := mkw 0x1fffeffbf6c7befe 0x23fffdff7ed8f7df 0xffffffffffc7ffff 0xfffffffffff8ffff

def z564 : W := mkw 0x00008021000020a4 0x0000100420000414 0x000180030004e060 0x4000300060009c0c

def z565 : W := mkw 0x2191b46d40d9e7af 0x0432368da81b3cf5 0x23c1f07c01f8e384 0x04783e0f803f1c70

def z566 : W := mkw 0x011100004081800a 0x0022200008103001 0x00300000c0030018 0x0006000018006003

def z567 : W := mkw 0x882a10002db7c000 0x1105420005b6f800 0xfc3e00003fffe003 0xdf87c00007fffc00

def z568 : W := mkw 0x9fffdfe3fff7fefe 0x13fffbfc7ffeffdf 0xffffffe3ffffffff 0xfffffffc7fffffff

def z569 : W := mkw 0x9b7b50002df7e6ae 0x136f6a0005befcd5 0xfffff0003fffffff 0xdffffe0007ffffff

def z570 : W := mkw 0x9b7950000db3c000 0x136f2a0001b67800 0x7ff1f0000ffbe005 0x0ffe3e0001ff7c00

def z571 : W := mkw 0x0000100000104000 0x0000020000020800 0x2041f0000038e004 0x04083e0000071c00

def z572 : W := mkw 0x1ff94e50c0000000 0x23ff29ca18000000 0x1ffffc00c0000007 0xc3ffff8018000000

def z573 : W := mkw 0x56400a941b681f00 0x0ac80152836d03e0 0xfc40039c3ff81f82 0x1f88007387ff03f0

def z574 : W := mkw 0x12c0045000000000 0x0258008a00000000 0x03c0007c00000004 0x0078000f80000000

def z575 : W := mkw 0x93d1d46149f1e6ae 0x127a3a8c293e3cd5 0xe3f1fc63c1fffffd 0xfc7e3f8c783fffff

def z576 : W := mkw 0x0191846140c1a6ae 0x0032308c281834d5 0x00318c63c007fff8 0x6006318c7800ffff

def z577 : W := mkw 0x33d7f5ff701c71e5 0x267afebfee038e3c 0xa3cff3ff303cf3e6 0xf479fe7fe6079e7c

def z578 : W := mkw 0x2006318e301c71e5 0x0400c631c6038e3c 0xa04e739c303cf3e2 0x1409ce7386079e7c

def z579 : W := mkw 0x2117b12b6095e0ef 0x0422f6256c12bc1d 0x003ff003c007e078 0x4007fe007800fc0f

def z580 : W := mkw 0x9b7b50002497c000 0x136f6a000492f800 0x1ffff0000007e007 0xc3fffe000000fc00

def z581 : W := mkw 0x0191044040c1860a 0x00322088081830c1 0xe3b18c00c1c7ec1d 0xdc7631801838fd83

def z582 : W := mkw 0xa93ff1af349ff1e5 0x1527fe35e693fe3c 0xa07ff3ff303ff3e6 0xf40ffe7fe607fe7c

def z583 : W := mkw 0x082a000024060000 0x010540000480c000 0x1c0e00003e000002 0x0381c00007c00000

def z584 : W := mkw 0x0191846140c1a6ae 0x0032308c281834d5 0x23b18c63c1c0e385 0xe476318c78381c70

def z585 : W := mkw 0x00000000004026ae 0x00000000000804d5 0x0000000000001ff8 0x00000000000003ff

def z586 : W := mkw 0x011310002095c000 0x002262000412b800 0xe3fff00031ffe007 0xdc7ffe00063ffc00

def z587 : W := mkw 0x7eeebfffbf7e7ff5 0x0fddd7fff7efcffe 0xffffffffffffffff 0xffffffffffffffff

def z588 : W := mkw 0x1ffdefffd0081100 0x23ffbdfffa010220 0xbffffffff0381387 0xf7fffffffe070270

def z589 : W := mkw 0x0db98e61c6c3aebe 0x01b731cc38d875d7 0xffb18c63cfc7fffd 0xfff6318c79f8ffff

def z590 : W := mkw 0xb351f02d09b9e1a5 0x166a3e05a1373c34 0x23c1f07c01f8e384 0x04783e0f803f1c70

def z591 : W := mkw 0x56400a100b200800 0x0ac8014201640100 0x1c0000000e000000 0x0380000001c00000

def z592 : W := mkw 0x0191846140c1a6ae 0x0032308c281834d5 0xe381806001c7fffc 0x1c70300c0038ffff

def z593 : W := mkw 0x935350002db7c000 0x126a6a0005b6f800 0xe3c1f0003fffe004 0x1c783e0007fffc00

def z594 : W := mkw 0x0cacaf7bc0000000 0x219595ef78000000 0x1c3e0fffc0000003 0xe387c1fff8000000

def z595 : W := mkw 0x400000841b681f00 0x08000010836d03e0 0xe04003fc3ff81f86 0xbc08007f87ff03f0

def z596 : W := mkw 0x0191846140c1a6ae 0x0032308c281834d5 0x43b00c63c1c31ff9 0x2876018c783863ff

def z597 : W := mkw 0x52c004d419681700 0x0a58009a832d02e0 0xa3c003fc31f81386 0xb478007f863f0270

def z598 : W := mkw 0x2c2eabafb60e39f5 0x0585d575f6c1c73e 0xdc3e0ffffe071ffb 0xfb87c1ffffc0e3ff

def z599 : W := mkw 0x0c2e0b82b6061850 0x0185c17056c0c30a 0x1c3e0383fe07007a 0x4387c0707fc0e00f

def z600 : W := mkw 0x082e0182b4061050 0x0105c0305680c20a 0x803e0383f007107a 0xf007c0707e00e20f

def z601 : W := mkw 0x57d10ed41be99f00 0x0afa21da837d33e0 0xfff18ffc3fffff87 0xfffe31ff87fffff0

def z602 : W := mkw 0x9b7b50843dbfd100 0x136f6a1087b7fa20 0xfffff3fc3ffff387 0xfffffe7f87fffe70

def z603 : W := mkw 0x04000a0082000810 0x0080014010400102 0x00000c00c0000c18 0x0000018018000183

def z604 : W := mkw 0x9b7b50002db7c000 0x136f6a0005b6f800 0x23fff00001ffe004 0x447ffe00003ffc00

def z605 : W := mkw 0x082e0102a4060050 0x0105c0205480c00a 0x000e000000000000 0x0001c00000000000

def z606 : W := mkw 0x2197b5ef70ddf7ef 0x0432f6bdee1bbefd 0xa3cff3ff31fcf3e6 0xf479fe7fe63f9e7c

def z607 : W := mkw 0x2c2ebbafb01c71e5 0x0585d775f6038e3c 0xbc7ffffff03cf3e7 0xf78ffffffe079e7c

def z608 : W := mkw 0x56c00ed41b681f00 0x0ad801da836d03e0 0x1c400ffc3e381f82 0x238801ff87c703f0

def z609 : W := mkw 0x04800e50c0000000 0x209001ca18000000 0x00000c00c0000000 0x0000018018000000

def z610 : W := mkw 0x56400a941b281900 0x0ac8015283650320 0xffc0039c3ff80007 0x9ff8007387ff0000

def z611 : W := mkw 0x5e6c6b9e9b281900 0x2bcd8d73d3650320 0x1c4e739c3e380002 0x0389ce7387c70000

def z612 : W := mkw 0x419184e55be9bfae 0x0832309cab7d37f5 0xe3b18c63fffffffd 0xfc76318c7fffffff

def z613 : W := mkw 0x04060b82b2041850 0x0080c1705640830a 0x800e0f83f0041c7a 0xf001c1f07e00838f

def z614 : W := mkw 0x0000000006020810 0x0000000000c04102 0x400000000e030c18 0x0800000001c06183

def z615 : W := mkw 0x800210803fb7d850 0x1000421007f6fb0a 0xe00000003ffffc78 0x1c00000007ffff8f

def z616 : W := mkw 0x9b7b50002db7c000 0x136f6a0005b6f800 0xffb000003fffe001 0x1ff6000007fffc00

def z617 : W := mkw 0x2006b1af301c71e5 0x0400d635e6038e3c 0x000ff3ff0004f3e0 0x6001fe7fe0009e7c

def z618 : W := mkw 0x0191044000c18600 0x00322088001830c0 0xe3b18c6001c7ff85 0xfc76318c0038fff0

def z619 : W := mkw 0x5e6e0b96bf2e1950 0x0bcdc172d7e5c32a 0xdc7e0f9ffe3f1c7b 0xfb8fc1f3ffc7e38f

def z620 : W := mkw 0x17d1ee7940000000 0x22fa3dcf28000000 0x1fc1fffc00000007 0xa3f83fff80000000

def z621 : W := mkw 0x1240000000000000 0x0248000000000000 0x1fc0000000000007 0x83f8000000000000

def z622 : W := mkw 0x2006318e301c5141 0x0400c631c6038a28 0x804e739f303c1062 0xf009ce73e607820c

def z623 : W := mkw 0x0c2e0b82b6061850 0x0185c17056c0c30a 0xdc0e03803e071c7a 0x1b81c07007c0e38f

def z624 : W := mkw 0x9f7f7b1aadb7c000 0x33efef6355b6f800 0xfffff39c3fffe007 0xdffffe7387fffc00

def z625 : W := mkw 0x76463b9e3b3c5941 0x0ec8c773c7678b28 0x1c4e739c3e380002 0x0389ce7387c70000

def z626 : W := mkw 0x2086b5ef705c77ef 0x0410d6bdee0b8efd 0xa04ffffff03cfffe 0xf409fffffe079fff

def z627 : W := mkw 0x00808461404026ae 0x0010108c280804d5 0xc0300c63c0071ff9 0xf806018c7800e3ff

def z628 : W := mkw 0x9bfbd4616db7c000 0x137f7a8c2db6f800 0xfffffc63ffffe007 0xffffff8c7ffffc00

def z629 : W := mkw 0x9b7f51823db7d040 0x136fea3047b6fa08 0xfffff3833ffff067 0xfffffe7067fffe0c

def z630 : W := mkw 0x3fffff7be01460e5 0x27ffffef7c028c1c 0x1fffffffc004e067 0xe3fffffff8009c0c

def z631 : W := mkw 0x0c2e0b82b6c7befe 0x0185c17056d8f7df 0xfc3e0f83ffc7fffb 0xff87c1f07ff8ffff

def z632 : W := mkw 0x9a6a50002d364000 0x134d4a0005a6c800 0xffce70003ff80007 0x9ff9ce0007ff0000

def z633 : W := mkw 0xb357f1af39bdf1e5 0x166afe35e737be3c 0xa3cff3ff31fcf3e6 0xf479fe7fe63f9e7c

def z634 : W := mkw 0x0c2a0a8036061800 0x0185415006c0c300 0xdc3e0f803e071c03 0xfb87c1f007c0e380

def z635 : W := mkw 0x0000000000400600 0x00000000000800c0 0xe000000001c01f80 0x1c000000003803f0

def z636 : W := mkw 0x9b7b50002db7c000 0x136f6a0005b6f800 0x1c7ff0003e3fe002 0x438ffe0007c7fc00

def z637 : W := mkw 0x082e0182b6061850 0x0105c03056c0c30a 0xc03e0003fe071c78 0x5807c0007fc0e38f

def z638 : W := mkw 0x9ff94e50cda38000 0x33ff29ca19b47000 0x5fb00c00cfc30001 0x0bf6018019f86000

def z639 : W := mkw 0x56c4afffdb681f00 0x2ad895fffb6d03e0 0xffc00ffffff81f87 0xbff801ffffff03f0

def z640 : W := mkw 0x0111000000000000 0x0022200000000000 0x03b1800000000005 0xc076300000000000

def z641 : W := mkw 0x13d1445040000000 0x227a288a08000000 0x0380000000000000 0x0070000000000000

def z642 : W := mkw 0x000000000081a0ae 0x0000000000103415 0x000000000007e078 0x000000000000fc0f

def z643 : W := mkw 0x800210002df7e6ae 0x1000420005befcd5 0xe00000003ffffff8 0x1c00000007ffffff

def z644 : W := mkw 0x0c2e0b82b6061850 0x0185c17056c0c30a 0xdc3e03803e070003 0xdb87c07007c0e000

def z645 : W := mkw 0x0111802140c1a6ae 0x00223004281834d5 0xe0318003c1c7fff8 0x5c0630007838ffff

def z646 : W := mkw 0x0080044000400600 0x00100088000800c0 0xe3b00c63c1c71ffd 0xfc76018c7838e3ff

def z647 : W := mkw 0x011180214081a0ae 0x0022300428103415 0x000180000000e000 0x0000300000001c00

def z648 : W := mkw 0x56c00ed41b281900 0x0ad801da83650320 0x1fc00ffc3e380007 0xa3f801ff87c70000

def z649 : W := mkw 0x0006a1ab30041040 0x0000d43566008208 0x804ff3ff30041066 0xf009fe7fe600820c

def z650 : W := mkw 0x1bf9e47940000000 0x237f3c8f28000000 0x1ffff07c00000007 0xc3fffe0f80000000

def z651 : W := mkw 0x56c21ed43b7c5f00 0x0ad843da876f8be0 0xffcffffc3ffcff87 0xfff9ffff87ff9ff0

def z652 : W := mkw 0x0080044000000000 0x0010008800000000 0x03800c6000000005 0xa070018c00000000

def z653 : W := mkw 0x0191846140400600 0x0032308c280800c0 0xe3b18c63c1c01f85 0xfc76318c783803f0

def z654 : W := mkw 0x1b7b400024060000 0x036f68000480c000 0xdffff0003e070007 0xdbfffe0007c0e000

def z655 : W := mkw 0x9bf9c4614de3a6ae 0x137f388c29bc74d5 0xffb18c63cfc7fffd 0xfff6318c79f8ffff

def z656 : W := mkw 0x56c20ed43f6e1f50 0x0ad841da87edc3ea 0xffc00ffc3fff1fff 0xbff801ff87ffe3ff

def z657 : W := mkw 0x0c2e0b02a4060050 0x0185c1605480c00a 0x1c3e0f83c007007b 0xe387c1f07800e00f

def z658 : W := mkw 0x7646bbbf3b3c79e5 0x0ec8d777e7678f3c 0xbc4ff3ff3e3cf3e6 0xf789fe7fe7c79e7c

def z659 : W := mkw 0x3ffffffff61e79f5 0x27fffffffec3cf3e 0xfffffffffe3fffff 0xffffffffffc7ffff

def z660 : W := mkw 0x019384e176c7befe 0x0032709c2ed8f7df 0xe3b18c63ffc7fffd 0xfc76318c7ff8ffff

def z661 : W := mkw 0x924210002db7c000 0x1248420005b6f800 0xffc000003fffe007 0x9ff8000007fffc00

def z662 : W := mkw 0x9bfbd4616df7e6ae 0x137f7a8c2dbefcd5 0xfffff0603fffe387 0xdffffe0c07fffc70

def z663 : W := mkw 0x1240000009200000 0x0248000001240000 0x1c4000003e380002 0x0388000007c70000

def z664 : W := mkw 0x082a100024164000 0x010542000482c800 0xfc7ff0003e3fe007 0xdf8ffe0007c7fc00

def z665 : W := mkw 0x0c280a8096021810 0x0185015012c04302 0xdc300f80fe031c1b 0xbb8601f01fc06383

def z666 : W := mkw 0x56c00ed41b681f00 0x0ad801da836d03e0 0x5f800ffc0fc01f81 0x2bf001ff81f803f0

def z667 : W := mkw 0x56c00e500b600e00 0x0ad801ca016c01c0 0xff800c600fc01f85 0xbff0018c01f803f0

def z668 : W := mkw 0x0002000024060050 0x000040000480c00a 0x0000000000070078 0x000000000000e00f

def z669 : W := mkw 0x0002100020144000 0x0000420004028800 0x000ff0000004e000 0x4001fe0000009c00

def z670 : W := mkw 0xdfff5fd6bfffdf50 0x1bffebfad7fffbea 0xffffffffffffffff 0xffffffffffffffff

def z671 : W := mkw 0x2484afffd00831e5 0x249095fffa01063c 0x00000fffc00013e0 0x200001fff800027c

def z672 : W := mkw 0x0111000000818000 0x0022200000103000 0x2381800001c0e004 0x0470300000381c00

def z673 : W := mkw 0x13d1e47940000000 0x227a3c8f28000000 0x03f1fc7fc0000005 0xe07e3f8ff8000000

def z674 : W := mkw 0xdeea5ed43f7e5f00 0x1bdd4bda87efcbe0 0xffce7ffc3ff81f87 0xbff9cfff87ff03f0

def z675 : W := mkw 0x16c00ed012001800 0x02d801da02400300 0xdfc00ffc3e001c07 0xbbf801ff87c00380

def z676 : W := mkw 0x408004c41b681f00 0x08100098836d03e0 0xe3800c603ff81f85 0xbc70018c07ff03f0

def z677 : W := mkw 0x0595af7bc0000000 0x20b2b5ef78000000 0x03b18fffc0000005 0xe07631fff8000000

def z678 : W := mkw 0x0000000400080100 0x0000000080010020 0x2040007c00380384 0x0408000f80070070

def z679 : W := mkw 0x5eee0fd2bf661e50 0x0bddc1fa57ecc3ca 0xdfbe0f83ffc71c7b 0xfbf7c1f07ff8e38f

def z680 : W := mkw 0x000080a5100831a4 0x00001014a2010634 0xa04183ff303cf3e6 0xf408307fe6079e7c

def z681 : W := mkw 0x00008021400020ae 0x0000100428000415 0x00000003c0000078 0x000000007800000f

def z682 : W := mkw 0x9f794a008fa38810 0x13ef294011f47102 0x5fb00c00cfc30c19 0x0bf6018019f86183

def z683 : W := mkw 0x9351500009b1c000 0x126a2a0001363800 0xffc1f0003ff8e007 0x9ff83e0007ff1c00

def z684 : W := mkw 0x3e6e7b9eb01c5141 0x27cdcf73d6038a28 0x1c4e739c30380002 0x0389ce7386070000

def z685 : W := mkw 0x2117b1af309df1e5 0x0422f635e613be3c 0xe3fff3ff31fff3e7 0xfc7ffe7fe63ffe7c

def z686 : W := mkw 0x0000008012001800 0x0000001002400300 0xc00000003e001c00 0x1800000007c00380

def z687 : W := mkw 0x20021000201460e5 0x0400420004028c1c 0x000000000004e060 0x0000000000009c0c

def z688 : W := mkw 0x1240000009200000 0x0248000001240000 0x5f8000000fc00001 0x0bf0000001f80000

def z689 : W := mkw 0x2dbfbfeff6dfffff 0x05b7f7fdfedbffff 0xffffffffffffffff 0xffffffffffffffff

def z690 : W := mkw 0x44000a9412081900 0x0880015282410320 0x0000039c00000000 0x0000007380000000

def z691 : W := mkw 0x44840fd692481f50 0x089081fad24903ea 0x00000fffc0001ff8 0x200001fff80003ff

def z692 : W := mkw 0x9b79500009b1c000 0x136f2a0001363800 0x3ffff00001f8e007 0xc7fffe00003f1c00

def z693 : W := mkw 0xdffb5e502ff7ce00 0x1bff6bca05fef9c0 0xfffffc003fffec07 0xdfffff8007fffd80

def z694 : W := mkw 0x2006b1af301c5141 0x0400d635e6038a28 0x004ff3ff30380006 0xe009fe7fe6070000

def z695 : W := mkw 0x9f7b5a803fb7d800 0x13ef6b5007f6fb00 0xffffff803ffffc07 0xfffffff007ffff80

def z696 : W := mkw 0x93d1f47949b1c000 0x327a3e8f29363800 0x23c1f07c01f8e004 0x04783e0f803f1c00

def z697 : W := mkw 0x2c2ebbabb61678f5 0x0585d77576c2cf1e 0xdc3fff83fe07fc7b 0xfb87fff07fc0ff8f

def z698 : W := mkw 0x9f7f5b82bfb7d850 0x13efeb7057f6fb0a 0xfffff3803fffe007 0xdffffe7007fffc00

def z699 : W := mkw 0x082e0102a4060050 0x0105c0205480c00a 0xc03e0c03c0071c79 0xf807c1807800e38f

def z700 : W := mkw 0x9ffffffbffb7d850 0x33ffffff7ff6fb0a 0xfffffffffffffc7f 0xffffffffffffff8f

def z701 : W := mkw 0x9b7f5102adb7c050 0x136fea2055b6f80a 0xfffff003ffffe07f 0xdffffe007ffffc0f

def z702 : W := mkw 0x0000000000000000 0x0000000000000000 0x00300c03c0000001 0xe006018078000000

def z703 : W := mkw 0x0000000000000000 0x0000000000000000 0xa00180000004e004 0xd400300000009c00

def z704 : W := mkw 0x9b7940000da38000 0x136f280001b47000 0xffb180000fc7e005 0xdff6300001f8fc00

def z705 : W := mkw 0x9351400009a18000 0x126a280001343000 0x0380000001c00000 0x0070000000380000

def z706 : W := mkw 0x45918ef552c9bfae 0x08b231deaa5937f5 0xe3b18fffc1c7fffd 0xfc7631fff838ffff

def z707 : W := mkw 0xa00210843dfff7ef 0x1400421087bffefd 0xe00000003ffffff8 0x1c00000007ffffff

def z708 : W := mkw 0x5ff94e50cbe18e0a 0x2bff29ca197c31c1 0x5fb00c00cfc30c19 0x0bf6018019f86183

def z709 : W := mkw 0x082c610a80000000 0x21058c2150000000 0x004e739c00000002 0x0009ce7380000000

def z710 : W := mkw 0x16c42f5a00000000 0x02d885eb40000000 0x1fce7ffc00000007 0xa3f9cfff80000000

def z711 : W := mkw 0x9b7b50002db7c000 0x136f6a0005b6f800 0xfffff3fc3fffe007 0xfffffe7f87fffc00

def z712 : W := mkw 0x56c00ed41b681f00 0x0ad801da836d03e0 0x3fc00ffc3ff80387 0xa7f801ff87ff0070

def z713 : W := mkw 0x93d1f47949f1e6ae 0x327a3e8f293e3cd5 0x23c1f07c01f8e384 0x04783e0f803f1c70

def z714 : W := mkw 0x53d1e47d49e9a7ae 0x2a7a3c8fa93d34f5 0x23c1f07c01f8e384 0x04783e0f803f1c70

def z715 : W := mkw 0x1e6ceb3b800020a4 0x23cd9d6770000414 0xbc4ff3ff0004f3e6 0xf789fe7fe0009e7c

def z716 : W := mkw 0x082a008036061850 0x0105401006c0c30a 0xdc3e0c03fe071c7b 0xfb87c1807fc0e38f

def z717 : W := mkw 0x9ffdef7bcd220000 0x33ffbdef79a44000 0x1fffffffce000007 0xe3fffffff9c00000

def z718 : W := mkw 0x0c2a0a80b6061850 0x0185415016c0c30a 0xdc300c03fe071c79 0xfb8601807fc0e38f

def z719 : W := mkw 0x2004b12f001861a5 0x04009625e0030c34 0xa04ff3ff003cf3e6 0xf409fe7fe0079e7c

def z720 : W := mkw 0xa00210843dbfd141 0x1400421087b7fa28 0xe00000003fffe000 0x1c00000007fffc00

def z721 : W := mkw 0x97555b829bb1d850 0x12eaab7053763b0a 0x23c1ff83c1f8fc7c 0x24783ff0783f1f8f

def z722 : W := mkw 0x082e018234061040 0x0105c0304680c208 0xdc3e0f83fe071c7b 0xfb87c1f07fc0e38f

def z723 : W := mkw 0x2484afefd2483fff 0x049095fdfa4907ff 0x00000fffc0001ff8 0x200001fff80003ff

def z724 : W := mkw 0x208214c4305c77e5 0x04104298860b8efc 0xe3800c6031fcffe5 0xbc70018c063f9ffc

def z725 : W := mkw 0x1ffdef7bc0c1a6ae 0x23ffbdef781834d5 0x7fffffffc1c3ef9f 0xeffffffff8387df3

def z726 : W := mkw 0x04040b8292001850 0x008081705240030a 0xdc300f83fe071c7b 0xfb8601f07fc0e38f

def z727 : W := mkw 0x0115a12b00818000 0x0022b42560103000 0xe3fff3ff01c7e007 0xfc7ffe7fe038fc00

def z728 : W := mkw 0x1ffdef7bc0c1a6ae 0x23ffbdef781834d5 0x5fffffffc1c31fff 0xebfffffff83863ff

def z729 : W := mkw 0x2c2a1a84b61e79f5 0x0585435096c3cf3e 0xfc300c00fe3ffff9 0x1f8601801fc7ffff

def z730 : W := mkw 0x16c4af7bc0000000 0x22d895ef78000000 0x1fcfffffc0000007 0xe3f9fffff8000000

def z731 : W := mkw 0x2006b12f201c61a5 0x0400d625e4038c34 0xa04ff3ff303ce386 0xf409fe7fe6079c70

def z732 : W := mkw 0x493de1afdb681f00 0x2927bc35fb6d03e0 0xe03ff003fff81f80 0x5c07fe007fff03f0

def z733 : W := mkw 0x2006b1af301c71e5 0x0400d635e6038e3c 0xa07ffffff03cf3e7 0xf40ffffffe079e7c

def z734 : W := mkw 0x56c00ed41b681f00 0x0ad801da836d03e0 0xfff00ffffff81f87 0xfffe01ffffff03f0

def z735 : W := mkw 0x0c280a0086020810 0x0185014010c04102 0x5c300c03ce031c79 0x2b86018079c0638f

def z736 : W := mkw 0x6484afff92483ff5 0x0c9095fff24907fe 0x00000fffc0001ff8 0x200001fff80003ff

def z737 : W := mkw 0x1ffdef7bc0818000 0x23ffbdef78103000 0x3fffffffc1c0e007 0xe7fffffff8381c00

def z738 : W := mkw 0x1f7deb3bc0000000 0x23efbd6778000000 0x1c7ff3ffc0000006 0xe38ffe7ff8000000

def z739 : W := mkw 0x2c28ba2d861a69b5 0x05851745b0c34d36 0x7c71fc7cce3bef9d 0x0f8e3f8f99c77df3

def z740 : W := mkw 0x60021084397c77e5 0x0c004210872f8efc 0xa000000031fcf3e0 0x14000000063f9e7c

def z741 : W := mkw 0x0c2c2b0a80000000 0x0185856150000000 0x1c4e739c00000002 0x0389ce7380000000

def z742 : W := mkw 0x0c2e2b9ab6061850 0x2185c57356c0c30a 0xdc3e0f9ffe071c7b 0xfb87c1f3ffc0e38f

def z743 : W := mkw 0x0191846140c1a6ae 0x0032308c281834d5 0x23b18c63c1c7fffc 0x6476318c7838ffff

def z744 : W := mkw 0x32421084393c71e5 0x0648421087278e3c 0xffc000003ffcf3e7 0x9ff8000007ff9e7c

def z745 : W := mkw 0x0195a56b40000000 0x0032b4ad68000000 0x03cff3ff00000006 0xe079fe7fe0000000

def z746 : W := mkw 0x56c00ed41b681f00 0x0ad801da836d03e0 0xfff00ffcfffb1f9f 0xbffe01ff9fff63f3

def z747 : W := mkw 0x1ffdef7bc0000000 0x23ffbdef78000000 0xdfffffffc0070007 0xfbfffffff800e000

def z748 : W := mkw 0x1ffdef7bc0c18600 0x23ffbdef781830c0 0xffffffffc1c7ff87 0xfffffffff838fff0

def z749 : W := mkw 0xcdbb5ed436dfdf00 0x19b76bda86dbfbe0 0x003ffffc0007ff80 0x6007ffff8000fff0

def z750 : W := mkw 0x1ffdef7bc0000000 0x23ffbdef78000000 0x1fffffffc007007f 0xe3fffffff800e00f

def z751 : W := mkw 0x211390a5709df1ef 0x04227214ae13be3d 0xa0318003f03ff3f8 0x540630007e07fe7f

def z752 : W := mkw 0x8486bf7bedb7c000 0x3090d7ef7db6f800 0xe0000fffffffe000 0x3c0001fffffffc00

def z753 : W := mkw 0x0c2c0b8292001800 0x0185817052400300 0xdc3e0f83fe071c7b 0xfb87c1f07fc0e38f

def z754 : W := mkw 0x0191044040c1a6ae 0x00322088081834d5 0xe3b00c03c1c7fff9 0xfc7601807838ffff

def z755 : W := mkw 0x2006b1af361e79f5 0x0400d635e6c3cf3e 0xa04ff3ff3e3cf3e6 0xf409fe7fe7c79e7c

def z756 : W := mkw 0x1e684a1000000000 0x03cd094200000000 0x1c4e739c00000002 0x0389ce7380000000

def z757 : W := mkw 0x219394e576dfffff 0x0432729caedbffff 0xe3b18c63fffffffd 0xfc76318c7fffffff

def z758 : W := mkw 0x1ffdef7bc2000810 0x23ffbdef78400102 0x1fffffffc0000c1f 0xe3fffffff8000183

def z759 : W := mkw 0x60021084325c7fe5 0x0c004210864b8ffc 0xa0000000303cffe0 0x1400000006079ffc

def z760 : W := mkw 0x1ffdef7bc0000000 0x23ffbdef78000000 0x1c7fffffc0000002 0x638ffffff8000000

def z761 : W := mkw 0x57518ab55ba9b9ae 0x0aea3156ab753735 0x1c71839ffe3fe07a 0x438e3073ffc7fc0f

def z762 : W := mkw 0x0c2c0b0286020850 0x0185816050c0410a 0x5c300c03ce030c79 0x0b86018079c0618f

def z763 : W := mkw 0x1ffdef7bc04026a4 0x23ffbdef780804d4 0xffffffffc1c4ffe7 0xfffffffff8389ffc

def z764 : W := mkw 0x2c2e1b86b61e5951 0x0585c370d6c3cb2a 0xdc3e0f83fe3f1c7b 0xfb87c1f07fc7e38f

def z765 : W := mkw 0x04020a8036061850 0x0080415006c0c30a 0xdc300f83fe071c7b 0xfb8601f07fc0e38f

def z766 : W := mkw 0x093de12bc0000000 0x2127bc2578000000 0x003ff3ffc0000000 0x6007fe7ff8000000

def z767 : W := mkw 0x1ffdef7bc0000000 0x23ffbdef78000000 0x1ffff3ffc0000006 0x43fffe7ff8000000

def z768 : W := mkw 0x04800ec412481f00 0x009001d8824903e0 0xffc00ffc3ff81f87 0xbff801ff87ff03f0

def z769 : W := mkw 0x76c6bf7b2b746ee5 0x0ed8d7ef656e8ddc 0x5f8ffc030fc4ec61 0x4bf1ff8061f89d8c

def z770 : W := mkw 0x1ffdef7bc04026ae 0x23ffbdef780804d5 0xffffffffc1c01fff 0xfffffffff83803ff

def z771 : W := mkw 0x9b79500009b1c000 0x136f2a0001363800 0xfffff0003ff8e007 0xdffffe0007ff1c00

def z772 : W := mkw 0x1ffd6f5ac0000000 0x23ffadeb58000000 0x1fce739c00000002 0x03f9ce7380000000

def z773 : W := mkw 0x0c2c6b1a80000000 0x21858d6350000000 0x000e739c00000000 0x0001ce7380000000

def z774 : W := mkw 0x219735ce70ddd74b 0x0432e6b9ce1bbae9 0x43fe7f9cf1fb0c1b 0x087fcff39e3f6183

def z775 : W := mkw 0x13d3e4f976061850 0x227a7c9f2ec0c30a 0xc3c1f07c3e071c7c 0x18783e0f87c0e38f

def z776 : W := mkw 0x20021084301c71e5 0x0400421086038e3c 0x200000003038e380 0x0400000006071c70

def z777 : W := mkw 0x20021084361e79f5 0x0400421086c3cf3e 0xa00000003e3cf3e0 0x1400000007c79e7c

def z778 : W := mkw 0x0c2e2b8ab6061850 0x0185c57156c0c30a 0xdc7e7f9ffe071c7b 0xfb8fcff3ffc0e38f

def z779 : W := mkw 0x0c2e0b02a6060850 0x0185c16054c0c10a 0x5c3e0f83ce070c7b 0xeb87c1f079c0e18f

def z780 : W := mkw 0x4484afffd2483fae 0x289095fffa4907f5 0x00000fffc0001ff8 0x200001fff80003ff

def z781 : W := mkw 0x1ffdef7bc081a0ae 0x23ffbdef78103415 0xffffffffc1c7e07f 0xfffffffff838fc0f

def z782 : W := mkw 0x1eec6f5a80000000 0x23dd8deb50000000 0x1ffe7fffc0000007 0xe3ffcffff8000000

def z783 : W := mkw 0x0006b12b201460a4 0x0000d62564028c14 0xa04ff3ff303cf3e6 0xf409fe7fe6079e7c

def z784 : W := mkw 0x2006b1af301c71e5 0x0400d635e6038e3c 0x004ff3ff303cf3e2 0x6009fe7fe6079e7c

def z785 : W := mkw 0x1eec6f5ac0000000 0x23dd8deb58000000 0x1c4e7f9cc0000002 0x0389cff398000000

def z786 : W := mkw 0x200290a5301c71e5 0x04005214a6038e3c 0xa0018060303cf3e4 0x1400300c06079e7c

def z787 : W := mkw 0x1ffdef7bc0000000 0x23ffbdef78000000 0x1fcfffffc0000006 0x23f9fffff8000000

def z788 : W := mkw 0x9ff94e50cde3860a 0x33ff29ca19bc70c1 0x5fb00c00cfc30c19 0x0bf6018019f86183

def z789 : W := mkw 0x09bde56bc0c1a6ae 0x2137bcad781834d5 0xe3ffffffc1c7ffff 0xfc7ffffff838ffff

def z790 : W := mkw 0x20021084301c71e5 0x0400421086038e3c 0xe0000000303ffff8 0x1c0000000607ffff

def z791 : W := mkw 0x56c00ed41b681f00 0x0ad801da836d03e0 0xbfc003fc3ff81386 0xb7f8007f87ff0270

def z792 : W := mkw 0x1ffdef7bc0000000 0x23ffbdef78000000 0xdfffffffc0001c07 0xfbfffffff8000380

def z793 : W := mkw 0x9aead4616d7666ae 0x135d5a8c2daeccd5 0x1c4e7c63fe381ffa 0x2389cf8c7fc703ff

def z794 : W := mkw 0x1ffdef7bc0000000 0x23ffbdef78000000 0x1fffffffc0001c7f 0xe3fffffff800038f

def z795 : W := mkw 0x9b7b50002db7c000 0x136f6a0005b6f800 0xfffffc03ffffe007 0xffffff807ffffc00

def z796 : W := mkw 0x082ce12b80000000 0x21059c2570000000 0x004ff3ff00000006 0xe009fe7fe0000000

def z797 : W := mkw 0x0084a56b40000000 0x001094ad68000000 0x004fffffc0000006 0xe009fffff8000000

def z798 : W := mkw 0x5aee0556ad6e0750 0x0b5dc0aad5adc0ea 0x23fe007fc1ff03fc 0x447fc00ff83fe07f

def z799 : W := mkw 0x73d1b47d49f9e7af 0x0e7a368fa93f3cf5 0x23c1f07c01f8e384 0x04783e0f803f1c70

def z800 : W := mkw 0x093b10002497c000 0x012762000492f800 0xfffff0003fffe007 0xdffffe0007fffc00

def z801 : W := mkw 0xbb7de1af1dabb1e5 0x176fbc35e3b5763c 0x5fb003ff0fc313e1 0x2bf6007fe1f8627c

def z802 : W := mkw 0xbe6e7b8ebf3e5951 0x17cdcf71d7e7cb2a 0x1c4e739c3e380002 0x0389ce7387c70000

def z803 : W := mkw 0x0191846140c1a6ae 0x0032308c281834d5 0xe3b00c63c1c7fff9 0x3c76018c7838ffff

def z804 : W := mkw 0x13d5e57b40c1a6ae 0x227abcaf681834d5 0xa3cff3ff01c4f3e6 0xf479fe7fe0389e7c

def z805 : W := mkw 0x0c2e0b02a4060000 0x0185c1605480c000 0xdc3e0f83fe071c7b 0xfb87c1f07fc0e38f

def z806 : W := mkw 0x1ffdef7bc0c1a6ae 0x23ffbdef781834d5 0xbfffffffc1c4f3e7 0xf7fffffff8389e7c

def z807 : W := mkw 0x20021084341e71f5 0x040042108683ce3e 0xa0000000303ff3f8 0x140000000607fe7f

def z808 : W := mkw 0x1ffdef7bc0000000 0x23ffbdef78000000 0x1fbfffffc0000001 0x63f7fffff8000000

def z809 : W := mkw 0x2006b1af301c71e5 0x0400d635e6038e3c 0x204ff3ff303ce3e6 0x4409fe7fe6079c7c

def z810 : W := mkw 0x20021084301c71e5 0x0400421086038e3c 0x00000000303813e0 0x000000000607027c

def z811 : W := mkw 0x53d1847149e1a6ae 0x0a7a308e293c34d5 0x2381806001c0e384 0x0470300c00381c70

def z812 : W := mkw 0x2006b1af301c71e5 0x0400d635e6038e3c 0xa0000003303cf3e0 0x1400000066079e7c

def z813 : W := mkw 0x16c00e5009600600 0x02d801ca012c00c0 0xffc00ffc3ff81f87 0xbff801ff87ff03f0

def z814 : W := mkw 0xc19314c43fffdf00 0x1832629887fffbe0 0xe3b18c603fffff85 0xfc76318c07fffff0

def z815 : W := mkw 0x0004a12b00000000 0x0000942560000000 0xa04ff3ff00001386 0xf409fe7fe0000270

def z816 : W := mkw 0x9b7b50002db7c000 0x136f6a0005b6f800 0x3ffff0003ff8e007 0xc7fffe0007ff1c00

def z817 : W := mkw 0x0dbdaf6bc0000000 0x01b7b5ed78000000 0x1fffffffc0000007 0xe3fffffff8000000

def z818 : W := mkw 0x0d3deb3bc0000000 0x21a7bd6778000000 0x003ff39fc0000000 0x4007fe73f8000000

def z819 : W := mkw 0xdff94e50cfe38e00 0x3bff29ca19fc71c0 0x5fb00c00cfc30c01 0x0bf6018019f86180

def z820 : W := mkw 0x0c2cab2b800020a4 0x0185956570000414 0xfc7fffffc007ffff 0xff8ffffff800ffff

def z821 : W := mkw 0x1ffdef7bc0c1a6ae 0x23ffbdef781834d5 0x1fffffffc007ffff 0xe3fffffff800ffff

def z822 : W := mkw 0x0c2e0b82b6061850 0x0185c17056c0c30a 0x5c3e0f83fe070c7b 0x4b87c1f07fc0e18f

def z823 : W := mkw 0x2006b1af301c71e5 0x0400d635e6038e3c 0xe3cff3ff31fcf3e7 0xfc79fe7fe63f9e7c

def z824 : W := mkw 0x2c2e3b8eb61e5951 0x0585c771d6c3cb2a 0xfc7e7ffffe3f1fff 0xff8fcfffffc7e3ff

def z825 : W := mkw 0x1ffd4f5280000000 0x03ffa9ea50000000 0x1fffffffc0000007 0xe3fffffff8000000

def z826 : W := mkw 0x1ffdef7bc9600600 0x23ffbdef792c00c0 0xfffffffffff81f87 0xffffffffffff03f0

def z827 : W := mkw 0x1244a12b00000000 0x0248942560000000 0x1fcff3ff00000007 0xe3f9fe7fe0000000

def z828 : W := mkw 0x0dbf8fe3f6c7befe 0x01b7f1fc7ed8f7df 0x3f8f83e03fc0e386 0x07f1f07c07f81c70

def z829 : W := mkw 0x56c00ed41b681f00 0x0ad801da836d03e0 0xffc18ffc3ffcff87 0xfff831ff87ff9ff0

def z830 : W := mkw 0x20021084393c71e5 0x0400421087278e3c 0xe00000003ffcf3e0 0x1c00000007ff9e7c

def z831 : W := mkw 0x0000000000000000 0x0000000000000000 0x004ff3fc00000006 0xe009fe7f80000000

def z832 : W := mkw 0x56c00ed41b681f00 0x0ad801da836d03e0 0x7fc00ffc3ff80f87 0x0ff801ff87ff01f0

def z833 : W := mkw 0xc19394e57fffffae 0x1832729caffffff5 0xe3b18c63fffffffd 0xfc76318c7fffffff

def z834 : W := mkw 0x1ffdef7bc9a18000 0x23ffbdef79343000 0xffffffffffffe007 0xfffffffffffffc00

def z835 : W := mkw 0x0484af7b00000000 0x009095ef60000000 0x004fffff00000006 0xe009ffffe0000000

def z836 : W := mkw 0x5ffdef7bc9600600 0x2bffbdef792c00c0 0x1fffffffc1c00007 0xe3fffffff8380000

def z837 : W := mkw 0x1eec6f5a80000000 0x23dd8deb50000000 0x1fce7f9c00000003 0x03f9cff380000000

def z838 : W := mkw 0x0004a12b00000000 0x0000942560000000 0x004ff3fc00000006 0x0009fe7f80000000

def z839 : W := mkw 0x0c2e6b8ab6061850 0x2185cd7156c0c30a 0xdc3e7f83fe071c7b 0xfb87cff07fc0e38f

def z840 : W := mkw 0x20021084301c5141 0x0400421086038a28 0xa000000030381380 0x1400000006070270

def z841 : W := mkw 0x0191846140c1a6ae 0x0032308c281834d5 0xe3f18fffc1c7ffff 0xfc7e31fff838ffff

def z842 : W := mkw 0x924210002db7c000 0x1248420005b6f800 0xffcff0003fffe007 0xdff9fe0007fffc00

def z843 : W := mkw 0x2002108436dfffff 0x0400421086dbffff 0xe00000003ffffff8 0x1c00000007ffffff

def z844 : W := mkw 0x16442b1a00000000 0x02c8856340000000 0x1c4e739c00000002 0x0389ce7380000000

def z845 : W := mkw 0x2004b12f001861a5 0x04009625e0030c34 0x204ff3fc0038e386 0x0409fe7f80071c70

def z846 : W := mkw 0x16400a841b281900 0x02c8015083650320 0xffc00ffc3ff81f87 0xbff801ff87ff03f0

def z847 : W := mkw 0x1e6c6b1a80c1a6ae 0x23cd8d63501834d5 0xfc4e739c01c7fffa 0x1f89ce738038ffff

def z848 : W := mkw 0x1ffdef7bc0000000 0x23ffbdef78000000 0xbfffffffc0001387 0xf7fffffff8000270

def z849 : W := mkw 0x1ffdef7bc4020000 0x23ffbdef78804000 0x5fffffffce030007 0xebfffffff9c06000

def z850 : W := mkw 0x0c2e0b86b60e1950 0x0185c170d6c1c32a 0xfc3e0f83fe3f1ffb 0xff87c1f07fc7e3ff

def z851 : W := mkw 0x5ffdef7bcb200800 0x2bffbdef79640100 0x1fffffffce000007 0xe3fffffff9c00000

def z852 : W := mkw 0x0c2c2b0a80000000 0x0185856150000000 0x1c7e7f9fc0000003 0xe38fcff3f8000000

def z853 : W := mkw 0x0595af7bc0000000 0x20b2b5ef78000000 0x03ffffffc0000007 0xe07ffffff8000000

def z854 : W := mkw 0x9353500029b5c000 0x126a6a000536b800 0xffcff0003ffce007 0xdff9fe0007ff9c00

def z855 : W := mkw 0x800210843dbfd100 0x1000421087b7fa20 0xe00000003ffff380 0x1c00000007fffe70

def z856 : W := mkw 0x1e6ceb3b80000000 0x23cd9d6770000000 0x1c4e73ff00000002 0x2389ce7fe0000000

def z857 : W := mkw 0x21131084309df1e5 0x042262108613be3c 0xe3b1800031fff3e5 0xdc763000063ffe7c

def z858 : W := mkw 0x2006b1af341e71e5 0x0400d635e683ce3c 0xe04ff3ff3e3ff3e6 0xfc09fe7fe7c7fe7c

def z859 : W := mkw 0x2006b1af301c71e5 0x0400d635e6038e3c 0xe04ff3ff303ffffe 0xfc09fe7fe607ffff

def z860 : W := mkw 0x1ffdef7bc0000000 0x23ffbdef78000000 0x1ffffffcc0000007 0x03ffffff98000000

def z861 : W := mkw 0x13d5e57b40000000 0x227abcaf68000000 0x03cff3fc00000006 0x0079fe7f80000000

def z862 : W := mkw 0x17d5ef7bc0000000 0x22fabdef78000000 0x03cfffffc0000006 0xe079fffff8000000

def z863 : W := mkw 0x2002b0ad301c71a5 0x04005615a6038e34 0xa04ff3fc303cf386 0xf409fe7f86079e70

def z864 : W := mkw 0xa002108439bdf1e5 0x140042108737be3c 0xa000000031fcf3e0 0x14000000063f9e7c

def z865 : W := mkw 0xa93ff12be497e0e5 0x3527fe257c92fc1c 0x003ff003c007e060 0x4007fe007800fc0c

def z866 : W := mkw 0x9ffdef7bcde3a6ae 0x33ffbdef79bc74d5 0xffffffffcfc7ffff 0xfffffffff9f8ffff

def z867 : W := mkw 0x9f7d6b1a8da38000 0x33efad6351b47000 0x5ffe739c0fc30003 0x0bffce7381f86000

def z868 : W := mkw 0x0191846140c1a6ae 0x0032308c281834d5 0xe3f18c63f1ffffff 0xfc7e318c7e3fffff

def z869 : W := mkw 0x56c00ed41b681f00 0x0ad801da836d03e0 0x5fc00ffc3ff81f83 0x2bf801ff87ff03f0

def z870 : W := mkw 0x04060b8232041840 0x0080c17046408308 0xdc3e0f83fe071c7b 0xfb87c1f07fc0e38f

def z871 : W := mkw 0x1ffd6f5a80000000 0x23ffadeb50000000 0x1ffffffc00000007 0xe3ffffff80000000

def z872 : W := mkw 0x0004210a00000000 0x0000842140000000 0x004ff39c00000006 0xc009fe7380000000

def z873 : W := mkw 0x1f7d6b1a80000000 0x23efad6350000000 0x1fffff9fc0000007 0xe3fffff3f8000000

def z874 : W := mkw 0x1ffdef7bc0000000 0x23ffbdef78000000 0xdffffffffe000007 0xfbffffffffc00000

def z875 : W := mkw 0x0084a56b404026ae 0x001094ad680804d5 0x004fffffc0001ffe 0xe009fffff80003ff

def z876 : W := mkw 0x9b7b5000adb7c010 0x136f6a0015b6f802 0xfffff000ffffe01f 0xdffffe001ffffc03

def z877 : W := mkw 0x2006b1af301c71e5 0x0400d635e6038e3c 0xa04ff3fc3038f386 0xb409fe7f86071e70

def z878 : W := mkw 0x04042b1a80000000 0x2080856350000000 0x004e739c00000002 0x0009ce7380000000

def z879 : W := mkw 0x1a6c610a00000000 0x034d8c2140000000 0x1c4e739c00000002 0x0389ce7380000000

def z880 : W := mkw 0x9ffdef7bcfa38810 0x33ffbdef79f47102 0x5fffffffcfc30c1f 0xebfffffff9f86183

def z881 : W := mkw 0x200290a5301c71e5 0x04005214a6038e3c 0xa0018003303cf3e0 0x5400300066079e7c

def z882 : W := mkw 0x3ffb5ed4f01c71e5 0x27ff6bda9e038e3c 0xbfb00c00f03cf3e1 0x17f601801e079e7c

def z883 : W := mkw 0x0dbdef7bc0c1a6ae 0x21b7bdef781834d5 0xe3bfffffc1c7fffd 0xfc77fffff838ffff

def z884 : W := mkw 0x5b7940841b681f00 0x0b6f2810836d03e0 0xfffff0003ff81f87 0xdffffe0007ff03f0

def z885 : W := mkw 0x1ffdef7bc040060a 0x23ffbdef780800c1 0x1fffffffc0000c1f 0xe3fffffff8000183

def z886 : W := mkw 0x2004b1af101871e5 0x04009635e2030e3c 0x204ff3ff0038f3e6 0xe409fe7fe0071e7c

def z887 : W := mkw 0x20021084301c71e5 0x0400421086038e3c 0xa0000060303cf3e4 0xb400000c06079e7c

def z888 : W := mkw 0x2006b1af361e79f5 0x0400d635e6c3cf3e 0xe07ffffffe3fffff 0xfc0fffffffc7ffff

def z889 : W := mkw 0x0404ab2b00000000 0x0080956560000000 0x1c4fffff00000007 0xe389ffffe0000000

def z890 : W := mkw 0x0c2a0a8036061800 0x0185415006c0c300 0xdc3e0f83fe071c7b 0xfb87c1f07fc0e38f

def z891 : W := mkw 0x0c2e0b82b6061850 0x0185c17056c0c30a 0xfc7e0f83fe3f1c7f 0xff8fc1f07fc7e38f

def z892 : W := mkw 0x93d1c46149e1a6ae 0x127a388c293c34d5 0x2381806001c0e384 0x0470300c00381c70

def z893 : W := mkw 0x1ffdef7bc0818000 0x23ffbdef78103000 0x5fffffffc1c30007 0xebfffffff8386000

def z894 : W := mkw 0x13d5e57b40c1a6ae 0x227abcaf681834d5 0xe3ffffffc1c7ffff 0xfc7ffffff838ffff

def z895 : W := mkw 0x1ffd6f5ac0c1860a 0x23ffadeb581830c1 0x5ffe7f9cc1c30c1b 0x0bffcff398386183

def z896 : W := mkw 0x0cacef7bc0000000 0x21959def78000000 0x000e7fffc0000000 0x2001cffff8000000

def z897 : W := mkw 0x1ff9ce7140000000 0x03ff39ce28000000 0x1fffffffc0000007 0xe3fffffff8000000

def z898 : W := mkw 0x0191e46940c1a6ae 0x20323c8d281834d5 0xe3b1fc63c1c7fffd 0xfc763f8c7838ffff

def z899 : W := mkw 0x56400a941b281900 0x0ac8015283650320 0xffc003fc3ff81387 0xbff8007f87ff0270

def z900 : W := mkw 0x0c2e0b86b60e1950 0x0185c170d6c1c32a 0xdc7e0f9ffe3f1c7b 0xfb8fc1f3ffc7e38f

def z901 : W := mkw 0x1ffdef7bc0000000 0x23ffbdef78000000 0x1ffe7fffc0000003 0x23ffcffff8000000

def z902 : W := mkw 0x16c00ed419281100 0x02d801da83250220 0xffc00ffc3ff81387 0xbff801ff87ff0270

def z903 : W := mkw 0x5e6c6b1a8b200800 0x2bcd8d6351640100 0x1c4e739c0e000002 0x0389ce7381c00000

def z904 : W := mkw 0x1a6a10002d364000 0x034d420005a6c800 0xfffff0003fffe007 0xdffffe0007fffc00

def z905 : W := mkw 0x600210843b3c79e5 0x0c00421087678f3c 0xa00000003e3cf3e0 0x1400000007c79e7c

def z906 : W := mkw 0x0191846140c1a6ae 0x0032308c281834d5 0xe3fffc63c1c7ffff 0xfc7fff8c7838ffff

def z907 : W := mkw 0x56c00ed41b681f00 0x0ad801da836d03e0 0xffc003fc3ff81f86 0x1ff8007f87ff03f0

def z908 : W := mkw 0x9a6a50002d364000 0x134d4a0005a6c800 0xffcff0003ffce007 0xdff9fe0007ff9c00

def z909 : W := mkw 0x20021084305c77e5 0x04004210860b8efc 0xe000000031fcffe0 0x1c000000063f9ffc

def z910 : W := mkw 0x1e6c6b1a80000000 0x23cd8d6350000000 0x1c7e739fc0000002 0x438fce73f8000000

def z911 : W := mkw 0x2006b1aff01c71e5 0x2400d635fe038e3c 0xa04ff3fff03cf3e6 0xf409fe7ffe079e7c

def z912 : W := mkw 0x1ffdef7bc0c1860a 0x23ffbdef781830c1 0xffffffffc1c31f9f 0xfffffffff83863f3

def z913 : W := mkw 0xc00210843fffdf50 0x1800421087fffbea 0xe00000003ffffff8 0x1c00000007ffffff

def z914 : W := mkw 0x56c00ed41b681f00 0x0ad801da836d03e0 0xff800ffc3ff81f81 0x3ff001ff87ff03f0

def z915 : W := mkw 0x093de12bc081a0ae 0x2127bc2578103415 0xa07ff3ffc007f3fe 0xf40ffe7ff800fe7f

def z916 : W := mkw 0x9ffdef7bcde3860a 0x33ffbdef79bc70c1 0x5fffffffcfc30c1f 0xebfffffff9f86183

def z917 : W := mkw 0x56c00ed49b681f10 0x0ad801da936d03e2 0xffc00ffcfff81f9f 0xbff801ff9fff03f3

def z918 : W := mkw 0x0c2e0b02a6060850 0x0185c16054c0c10a 0xdc3e0c03fe070c7b 0xdb87c1807fc0e18f

def z919 : W := mkw 0x1ffdef7bc6020810 0x23ffbdef78c04102 0xdfffffffce071c7f 0xfbfffffff9c0e38f

def z920 : W := mkw 0xb3d1f46d49f9e7af 0x167a3e8da93f3cf5 0x23c1f07c01f8e384 0x04783e0f803f1c70

def z921 : W := mkw 0x1ffdef7bc2000800 0x23ffbdef78400100 0x5fffffffce000c07 0xebfffffff9c00180

def z922 : W := mkw 0x1f7deb3bc0000000 0x23efbd6778000000 0x1c7fff9fc0000003 0xe38ffff3f8000000

def z923 : W := mkw 0x1e6c6b1a89200000 0x23cd8d6351240000 0x1c4e739c3e380002 0x0389ce7387c70000

def z924 : W := mkw 0x1eecef7b80000000 0x23dd9def70000000 0x1fcfffff00000007 0xe3f9ffffe0000000

def z925 : W := mkw 0x8c2e5b82b6165850 0x1185cb7056c2cb0a 0xdc3e7f83fe071c7b 0xfb87cff07fc0e38f

def z926 : W := mkw 0x4c2e0b96b60e1950 0x0985c172d6c1c32a 0xdc3e0f9ffe071c7b 0xfb87c1f3ffc0e38f

def z927 : W := mkw 0x9b7b50002db7c000 0x136f6a0005b6f800 0xfffff0603ffff387 0xfffffe0c07fffe70

def z928 : W := mkw 0x7e6e3b9ebf3e5951 0x0fcdc773d7e7cb2a 0x1c4e739c3e380002 0x0389ce7387c70000

def z929 : W := mkw 0xa0021084349ff1e5 0x140042108693fe3c 0xa0000000303ff3e0 0x140000000607fe7c

def z930 : W := mkw 0x0404ab2b80000000 0x0080956570000000 0x004fffffc0000006 0xe009fffff8000000

def z931 : W := mkw 0xe00210843fffffe5 0x1c00421087fffffc 0xe00000003fffffe0 0x1c00000007fffffc

def z932 : W := mkw 0x1b79400009a18000 0x036f280001343000 0xfffff0003fffe007 0xdffffe0007fffc00

def z933 : W := mkw 0x1f7deb3bc0000000 0x23efbd6778000000 0x1ffff39fc0000007 0xc3fffe73f8000000

def z934 : W := mkw 0x0080044000c1a6ae 0x00100088001834d5 0xe3b00c63c1c7fffd 0xfc76018c7838ffff

def z935 : W := mkw 0x9b7b50002db7c000 0x136f6a0005b6f800 0xfffffc003ffffc07 0xffffff8007ffff80

def z936 : W := mkw 0x1353100029b5c000 0x026a62000536b800 0xfffff0003fffe007 0xdffffe0007fffc00

def z937 : W := mkw 0x0c2e0b82b6061850 0x0185c17056c0c30a 0xdc7e0ffffe071c7f 0xfb8fc1ffffc0e38f

def z938 : W := mkw 0x9b7b50002db7c000 0x136f6a0005b6f800 0xffcff0003fffe006 0x1ff9fe0007fffc00

def z939 : W := mkw 0x2006b1af321c79e5 0x0400d635e6438f3c 0xe04ff3ff3e3cffe6 0xfc09fe7fe7c79ffc

def z940 : W := mkw 0x16c00e5000000000 0x02d801ca00000000 0x1fcffffc00000007 0xe3f9ffff80000000

def z941 : W := mkw 0x56c00ed41b681f00 0x0ad801da836d03e0 0x3fc00ffc3ff81f86 0x27f801ff87ff03f0

def z942 : W := mkw 0x5ffdef7bcbe1aeae 0x2bffbdef797c35d5 0xffffffffcfc7ffff 0xfffffffff9f8ffff

def z943 : W := mkw 0x093de12bc0000000 0x2127bc2578000000 0x007ff39fc0000002 0x400ffe73f8000000

def z944 : W := mkw 0x1ffdef7bc0000000 0x23ffbdef78000000 0xffffffffc1c00007 0xfffffffff8380000

def z945 : W := mkw 0x9b7b50002db7c000 0x136f6a0005b6f800 0xffbff0003fffe001 0x5ff7fe0007fffc00

def z946 : W := mkw 0x0c2e0b82b6061850 0x0185c17056c0c30a 0xdc7fff83fe071c7f 0xfb8ffff07fc0e38f

def z947 : W := mkw 0x2006b1af301c71e5 0x0400d635e6038e3c 0xa04ffffff03cfffe 0xf409fffffe079fff

def z948 : W := mkw 0x1ff9ee7940000000 0x23ff3dcf28000000 0x1ffffffc00000007 0xe3ffffff80000000

def z949 : W := mkw 0x219394e570ddf7ef 0x0432729cae1bbefd 0xa381806031fcf3e4 0x1470300c063f9e7c

def z950 : W := mkw 0x56c00ed41b681f00 0x0ad801da836d03e0 0xffc00fff3ffc1fe7 0xfff801ffe7ff83fc

def z951 : W := mkw 0x1e6c6b1a86020810 0x23cd8d6350c04102 0x1c4e739c0e000002 0x0389ce7381c00000

def z952 : W := mkw 0x0c2c0b8296021850 0x0185817052c0430a 0x5c3e0f83ce031c7b 0xeb87c1f079c0638f

def z953 : W := mkw 0xc00210843f3e5900 0x1800421087e7cb20 0x000000003e380000 0x0000000007c70000

def z954 : W := mkw 0x1ffdef7bc0000000 0x23ffbdef78000000 0x1fffff9fc0000003 0x43fffff3f8000000

def z955 : W := mkw 0x0c2e0b82b6061850 0x0185c17056c0c30a 0xffbe0f83ffc71c7f 0xfff7c1f07ff8e38f

def z956 : W := mkw 0x1f7deb2b80000000 0x03efbd6570000000 0x1fffffffc0000007 0xe3fffffff8000000

def z957 : W := mkw 0x1355e12b00000000 0x026abc2560000000 0x03cff3ff00000006 0xe079fe7fe0000000

def z958 : W := mkw 0x0595af7bc0c1a6ae 0x20b2b5ef781834d5 0xe3ffffffc1c7ffff 0xfc7ffffff838ffff

def z959 : W := mkw 0x2002108430ddf7ef 0x04004210861bbefd 0xa000000031fcf3e0 0x14000000063f9e7c

def z960 : W := mkw 0x1ff94e5000c18600 0x03ff29ca001830c0 0xfffffffc01c7ff87 0xffffffff8038fff0

def z961 : W := mkw 0x1ffd6f5ac0000000 0x23ffadeb58000000 0x1ffe7ffcc0000007 0xa3ffcfff98000000

def z962 : W := mkw 0x1e6ceb3b80000000 0x23cd9d6770000000 0x1c4ff3fc00000006 0x0389fe7f80000000

def z963 : W := mkw 0x20021084301c71e5 0x0400421086038e3c 0xa04ff3fc303cf3e6 0xf409fe7f86079e7c

def z964 : W := mkw 0x2006b1af301c71e5 0x0400d635e6038e3c 0xa07ff3fff03ff3fe 0xf40ffe7ffe07fe7f

def z965 : W := mkw 0x0004a12b00000000 0x0000942560000000 0xc07fffffc0071c7f 0xf80ffffff800e38f

def z966 : W := mkw 0x0404ab3b80000000 0x2080956770000000 0x004ff3ff00000006 0xe009fe7fe0000000

def z967 : W := mkw 0x1ffdef7bc0c1a6ae 0x23ffbdef781834d5 0xffffffffc1c7e387 0xfffffffff838fc70

def z968 : W := mkw 0x0828000004020000 0x0105000000804000 0xdc300c03ce071c79 0xfb86018079c0e38f

def z969 : W := mkw 0x13d1846149e1a6ae 0x027a308c293c34d5 0x23c1806001f8e384 0x0478300c003f1c70

def z970 : W := mkw 0x0004a12b00000000 0x0000942560000000 0x000ff3ff00000000 0x6001fe7fe0000000

def z971 : W := mkw 0xa11390a53dbff1e5 0x14227214a7b7fe3c 0xe3b180633ffff3e5 0xfc76300c67fffe7c

def z972 : W := mkw 0x2006b1af301c71e5 0x0400d635e6038e3c 0xfc4ff3ff3e3cf3e7 0xff89fe7fe7c79e7c

def z973 : W := mkw 0x400210843b7c5f00 0x08004210876f8be0 0xe00000003ffcff80 0x1c00000007ff9ff0

def z974 : W := mkw 0x5eec6f5a8b600e00 0x2bdd8deb516c01c0 0x5fce7f9c0fc00c03 0x0bf9cff381f80180

def z975 : W := mkw 0x0004210a00000000 0x0000842140000000 0x004e73fc00000006 0xa009ce7f80000000

def z976 : W := mkw 0x9b7b50002db7c050 0x136f6a0005b6f80a 0xfffff0003fffe07f 0xdffffe0007fffc0f

def z977 : W := mkw 0x52c004d419681700 0x0a58009a832d02e0 0xffc003fc3ff81387 0xbff8007f87ff0270

def z978 : W := mkw 0xbb7b50843dbff1e5 0x176f6a1087b7fe3c 0xffb000003ffff3e1 0x1ff6000007fffe7c

def z979 : W := mkw 0x0004a1af100831a4 0x00009435e2010634 0xa04ff3ff303cf3e6 0xf409fe7fe6079e7c

def z980 : W := mkw 0xde6e5b96bf3e5950 0x1bcdcb72d7e7cb2a 0x1c4e739c3e380002 0x0389ce7387c70000

def z981 : W := mkw 0x0484af7bc04026ae 0x209095ef780804d5 0xa04fffffc004fffe 0xf409fffff8009fff

def z982 : W := mkw 0x1ffdef7bc0400600 0x23ffbdef780800c0 0x1fffffffc0001f87 0xe3fffffff80003f0

def z983 : W := mkw 0x9ffdef7bcda38000 0x33ffbdef79b47000 0xfffffffffffb0007 0xffffffffffff6000

def z984 : W := mkw 0x0c2c0b0286020810 0x0185816050c04102 0xdc3e0f83ce071c7b 0xfb87c1f079c0e38f

def z985 : W := mkw 0x0dbdef7bc0000000 0x21b7bdef78000000 0x1c3fffffc0000003 0xe387fffff8000000

def z986 : W := mkw 0x0c2e0b82b6061850 0x0185c17056c0c30a 0xdc300f83fe071c79 0x3b8601f07fc0e38f

def z987 : W := mkw 0x0c2c0b8296021850 0x0185817052c0430a 0xdc300f83fe031c7b 0xbb8601f07fc0638f

def z988 : W := mkw 0x9e6c6b1a8d220000 0x33cd8d6351a44000 0x1c4e739c0e000002 0x0389ce7381c00000

def z989 : W := mkw 0x20021084301c71e5 0x0400421086038e3c 0xa0000003303cf3e0 0xf400000066079e7c

def z990 : W := mkw 0x893ff12be497e0ae 0x3127fe257c92fc15 0x003ff003c007e078 0x4007fe007800fc0f

def z991 : W := mkw 0x17d5af7b40000000 0x02fab5ef68000000 0x1fffffffc0000007 0xe3fffffff8000000

def z992 : W := mkw 0x20021084301c71e5 0x0400421086038e3c 0x000000000004f3e0 0x0000000000009e7c

def z993 : W := mkw 0x3ffdef7bc00020e5 0x27ffbdef7800041c 0x1fffffffc0000067 0xe3fffffff800000c

def z994 : W := mkw 0x2006b1af301c71e5 0x0400d635e6038e3c 0xa04ff3fc303ce386 0xd409fe7f86079c70

def z995 : W := mkw 0x1eecef7bc0000000 0x23dd9def78000000 0x1c7e7fffc0000003 0xe38fcffff8000000

def z996 : W := mkw 0x600210843bfdffef 0x0c004210877fbffd 0xe00000003ffffff8 0x1c00000007ffffff

def z997 : W := mkw 0x1ffdef7bc0818000 0x23ffbdef78103000 0x1fffffffc007e007 0xe3fffffff800fc00

def z998 : W := mkw 0x1f7d6b1a80000000 0x23efad6350000000 0x1ffe739c00000003 0x03ffce7380000000

def z999 : W := mkw 0x9b7b50002db7c000 0x136f6a0005b6f800 0xfffffc00ffffec1f 0xdfffff801ffffd83

def z1000 : W := mkw 0x0191a46940c1a6ae 0x0032348d281834d5 0xe3f1fc7fc1c7fffd 0xfc7e3f8ff838ffff

def z1001 : W := mkw 0x0191a47940c1a6ae 0x2032348f281834d5 0xe3b18c7fc1c7fffd 0xfc76318ff838ffff

def z1002 : W := mkw 0x0000000000000000 0x0000000000000000 0xdc300c03fe071c7b 0xfb8601807fc0e38f

def z1003 : W := mkw 0x1ffdef7bc081800a 0x23ffbdef78103001 0x1fffffffc003001f 0xe3fffffff8006003

def z1004 : W := mkw 0x2c2e3b8eb61e5951 0x0585c771d6c3cb2a 0xfc7fff9ffe3ffc7f 0xff8ffff3ffc7ff8f

def z1005 : W := mkw 0x0c2e1b86b61e5950 0x0185c370d6c3cb2a 0xfc7ffffffe3fffff 0xff8fffffffc7ffff

def z1006 : W := mkw 0x1e6c6b1a80000000 0x23cd8d6350000000 0x1c7e7f9cc0000003 0x038fcff398000000

def z1007 : W := mkw 0x1f7d6b1a80000000 0x23efad6350000000 0x1c7ff39c00000002 0x438ffe7380000000

def z1008 : W := mkw 0x1ffdef7bc00020a4 0x23ffbdef78000414 0x1fffffffc004e067 0xe3fffffff8009c0c

def z1009 : W := mkw 0x2006b1af321c79f5 0x0400d635e6438f3e 0xa04ff3ff303cfffe 0xf409fe7fe6079fff

def z1010 : W := mkw 0x1ffdef7bc0c1a6ae 0x23ffbdef781834d5 0xffffffffc1c0ff87 0xfffffffff8381ff0

def z1011 : W := mkw 0x1ffdef7bc0c1a6ae 0x23ffbdef781834d5 0x3fcff3fc01c0e386 0x07f9fe7f80381c70

def z1012 : W := mkw 0x5ffdef7bcb600e00 0x2bffbdef796c01c0 0xffffffffcfc01f87 0xfffffffff9f803f0

def z1013 : W := mkw 0x1ffdef7bc00020ae 0x23ffbdef78000415 0x1fffffffc000007f 0xe3fffffff800000f

def z1014 : W := mkw 0x0dbdaf6bc0c1a6ae 0x01b7b5ed781834d5 0xffffffffc1c7ffff 0xfffffffff838ffff

def z1015 : W := mkw 0x1eecaf7b80000000 0x03dd95ef70000000 0x1fffffffc0000007 0xe3fffffff8000000

def z1016 : W := mkw 0x12c4a57b00000000 0x025894af60000000 0x03cff3ff00000006 0xe079fe7fe0000000

def z1017 : W := mkw 0x0c2e1b82b6165850 0x0185c37056c2cb0a 0xfc3e0f83fe3ffc7b 0xff87c1f07fc7ff8f

def z1018 : W := mkw 0x0c2cab2b86020810 0x0185956570c04102 0x5c7fffffce030c1f 0xeb8ffffff9c06183

def z1019 : W := mkw 0xdffb5ed43fffdf00 0x1bff6bda87fffbe0 0xffb00c003fffff81 0x1ff6018007fffff0

def z1020 : W := mkw 0x1ffdef7bc0000000 0x23ffbdef78000000 0xbffffffff0380007 0xf7fffffffe070000

def z1021 : W := mkw 0x5ffdef7bcb600e00 0x2bffbdef796c01c0 0xfffffffffff80c07 0xffffffffffff0180

def z1022 : W := mkw 0x1ffdef7bc0000000 0x23ffbdef78000000 0x1fcff3ff00000006 0xe3f9fe7fe0000000

def z1023 : W := mkw 0x1eecef7bc0000000 0x23dd9def78000000 0x1fce7fffc0000007 0xa3f9cffff8000000

def z1024 : W := mkw 0x1ffdef7bc04026ae 0x23ffbdef780804d5 0xbfffffffc004ffff 0xf7fffffff8009fff

def z1025 : W := mkw 0x1bfde56b40000000 0x037fbcad68000000 0x1fffffffc0000007 0xe3fffffff8000000

def z1026 : W := mkw 0x56c00e5409680700 0x0ad801ca812d00e0 0xffc00ffc3ff80387 0xbff801ff87ff0070

def z1027 : W := mkw 0xdff94e500fe38e00 0x1bff29ca01fc71c0 0x5ffffffc0fc30c07 0xebffffff81f86180

def z1028 : W := mkw 0x0004a12b00000000 0x0000942560000000 0x007fffffc0000007 0xe00ffffff8000000

def z1029 : W := mkw 0x1eecef7bc0000000 0x23dd9def78000000 0x1c4fffffc0000006 0xe389fffff8000000

def z1030 : W := mkw 0x9ffdef7bcda38000 0x33ffbdef79b47000 0xffffffffcfc7e007 0xfffffffff9f8fc00

def z1031 : W := mkw 0x1f7d6b1a80000000 0x23efad6350000000 0x1fcff39c00000006 0x03f9fe7380000000

def z1032 : W := mkw 0x56c00ed4db681f00 0x2ad801da9b6d03e0 0xffc00ffcfff81f87 0xbff801ff9fff03f0

def z1033 : W := mkw 0x1ffdef7bc081a0a4 0x23ffbdef78103414 0xffffffffc1c7f3e7 0xfffffffff838fe7c

def z1034 : W := mkw 0x1ffdef7bc0000000 0x23ffbdef78000000 0xbfffffffc004e007 0xf7fffffff8009c00

def z1035 : W := mkw 0x1ffdef7bc0000000 0x23ffbdef78000000 0x9fffffffc0041067 0xf3fffffff800820c

def z1036 : W := mkw 0x9b7b5000edb7c000 0x336f6a001db6f800 0xfffff000ffffe007 0xdffffe001ffffc00

def z1037 : W := mkw 0x20021084301c71e5 0x0400421086038e3c 0xa0400000303cf3e6 0x9408000006079e7c

def z1038 : W := mkw 0x20021084321c79f5 0x0400421086438f3e 0xa0000000303cfff8 0x1400000006079fff

def z1039 : W := mkw 0x56c00ed41b681f00 0x0ad801da836d03e0 0xffcffffc3ff81f87 0xfff9ffff87ff03f0

def z1040 : W := mkw 0xa19394e57dfff7ef 0x1432729cafbffefd 0xe3b18c63fffffffd 0xfc76318c7fffffff

def z1041 : W := mkw 0x1e6c6b1a86020810 0x23cd8d6350c04102 0x5c7e7f9cce030c1b 0x0b8fcff399c06183

def z1042 : W := mkw 0x0004a12b00000000 0x0000942560000000 0x004ff39f00000002 0x4009fe73e0000000

def z1043 : W := mkw 0x2006b1af701c71ef 0x0400d635ee038e3d 0xa04ff3fff03cf3fe 0xf409fe7ffe079e7f

def z1044 : W := mkw 0x0004a12b000020a4 0x0000942560000414 0x004ff3ff0004e066 0xe009fe7fe0009c0c

def z1045 : W := mkw 0x00021084301c5100 0x0000421086038a20 0xa0000000303cf380 0x1400000006079e70

def z1046 : W := mkw 0x1f7deb3bc081a0ae 0x23efbd6778103415 0x1c7ff39fc007e07a 0x438ffe73f800fc0f

def z1047 : W := mkw 0x00808461004026a4 0x0010108c200804d4 0xe3b18c63c1c7fffd 0xfc76318c7838ffff

def z1048 : W := mkw 0x0d3deb2bc0000000 0x21a7bd6578000000 0x1c7fffffc0000007 0xe38ffffff8000000

def z1049 : W := mkw 0x2c2e3b8ab6165851 0x0585c77156c2cb0a 0xdc3e7f83fe071c7b 0xfb87cff07fc0e38f

def z1050 : W := mkw 0x600210843b3c5941 0x0c00421087678b28 0x000000003e380000 0x0000000007c70000

def z1051 : W := mkw 0x219314c470ddf7ef 0x043262988e1bbefd 0xe3b00c00f1fffff9 0x1c7601801e3fffff

def z1052 : W := mkw 0x17d5ef7b40000000 0x22fabdef68000000 0x1fcfffff00000007 0xe3f9ffffe0000000

def z1053 : W := mkw 0x6484afffd2483fe5 0x2c9095fffa4907fc 0x00000fffc0001fe0 0x200001fff80003fc

def z1054 : W := mkw 0x2006b1af301c71e5 0x0400d635e6038e3c 0x204ff3ff3038e386 0xe409fe7fe6071c70

def z1055 : W := mkw 0x1ffd6f5ac0000000 0x23ffadeb58000000 0x1ffe7f9fc0000003 0xe3ffcff3f8000000

def z1056 : W := mkw 0x1e6ceb3b80000000 0x23cd9d6770000000 0x1c4ff39f00000002 0x4389fe73e0000000

def z1057 : W := mkw 0x0c2e1b82b6165850 0x0185c37056c2cb0a 0xdc3fff83fe07fc7b 0xfb87fff07fc0ff8f

def z1058 : W := mkw 0x1e6c6b1a80000000 0x23cd8d6350000000 0x1c4e73fc00000006 0xa389ce7f80000000

def z1059 : W := mkw 0x0c280a0086020810 0x0185014010c04102 0x5c300c03ce070c79 0x4b86018079c0e18f

def z1060 : W := mkw 0x1ffdef7bc9200000 0x23ffbdef79240000 0x1ffffffffe380007 0xe3ffffffffc70000

def z1061 : W := mkw 0x0195a56b40c1860a 0x0032b4ad681830c1 0x43ffffffc1c30c1f 0xe87ffffff8386183

def z1062 : W := mkw 0x12c004c419681700 0x02580098832d02e0 0xffc00ffc3ff81f87 0xbff801ff87ff03f0

def z1063 : W := mkw 0x20021084361e5951 0x0400421086c3cb2a 0xc00000003e3f1c78 0x1800000007c7e38f

def z1064 : W := mkw 0x9ffdef7bc9a18000 0x33ffbdef79343000 0x1fffffffc1c00007 0xe3fffffff8380000

def z1065 : W := mkw 0x1ffdef7bc0c1a6ae 0x23ffbdef781834d5 0x5fffffffc1c7ec7f 0xebfffffff838fd8f

def z1066 : W := mkw 0x0195a56b40c1a6ae 0x0032b4ad681834d5 0x23cff3ff01c0e386 0xe479fe7fe0381c70

def z1067 : W := mkw 0x2006b1af301c71e5 0x0400d635e6038e3c 0xe04fffff303cffe7 0xfc09ffffe6079ffc

def z1068 : W := mkw 0x0084a56b00400600 0x001094ad600800c0 0xe3cfffff01c01f87 0xfc79ffffe03803f0

def z1069 : W := mkw 0xc00210843f7e5f00 0x1800421087efcbe0 0xe00000003ff81f80 0x1c00000007ff03f0

def z1070 : W := mkw 0x1ffdef7bc081a0ae 0x23ffbdef78103415 0xdfffffffc007fc7f 0xfbfffffff800ff8f

def z1071 : W := mkw 0x093de12b00000000 0x0127bc2560000000 0x007ff3ff00000006 0xe00ffe7fe0000000

def z1072 : W := mkw 0x20021084301c71e5 0x0400421086038e3c 0xe0300c03f03ffff9 0xfc0601807e07ffff

def z1073 : W := mkw 0x1b7de12bc0000000 0x236fbc2578000000 0x1ffff3ffc0000007 0xe3fffe7ff8000000

def z1074 : W := mkw 0xdff94e504fe38e0a 0x1bff29ca09fc71c1 0x5fb00c00cfc30c19 0x0bf6018019f86183

def z1075 : W := mkw 0x96c21e502db7c000 0x12d843ca05b6f800 0xffc00ffc3fffe007 0xbff801ff87fffc00

def z1076 : W := mkw 0x2006b1af341e71f5 0x0400d635e683ce3e 0xa04ff3ff303ff3fe 0xf409fe7fe607fe7f

def z1077 : W := mkw 0x5ffdef7bcbe18e0a 0x2bffbdef797c31c1 0x5fffffffcfc30c1f 0xebfffffff9f86183

def z1078 : W := mkw 0x0084a57b40000000 0x201094af68000000 0x004ff3ff00000006 0xe009fe7fe0000000

def z1079 : W := mkw 0x1eec6f5a80000000 0x23dd8deb50000000 0x1c4e7ffc00000002 0x2389cfff80000000

def z1080 : W := mkw 0x1ffdef7bc0000000 0x23ffbdef78000000 0x1ffff3fc00000007 0xc3fffe7f80000000

def z1081 : W := mkw 0x1644ab3b00000000 0x02c8956760000000 0x1c4ff3ff00000006 0xe389fe7fe0000000

def z1082 : W := mkw 0x1e6c6b1a80000000 0x23cd8d6350000000 0x1c4e7f9fc0000002 0x2389cff3f8000000

def z1083 : W := mkw 0x2006b1af301c71e5 0x0400d635e6038e3c 0xe07ff3ff303ff3e7 0xfc0ffe7fe607fe7c

def z1084 : W := mkw 0x1f7d6b1a80818000 0x23efad6350103000 0xfffff39c01c7e007 0xdffffe738038fc00

def z1085 : W := mkw 0x619394e57bfdffef 0x0c32729caf7fbffd 0xe3b18c63fffffffd 0xfc76318c7fffffff

def z1086 : W := mkw 0x0004a12b000020a4 0x0000942560000414 0x204ff3ff0000e386 0xe409fe7fe0001c70

def z1087 : W := mkw 0x0c2e0b82b6061850 0x0185c17056c0c30a 0x5c3e0f83fe031c7b 0x2b87c1f07fc0638f

def z1088 : W := mkw 0x0484af7bc0000000 0x209095ef78000000 0x004e7fffc0000002 0x2009cffff8000000

def z1089 : W := mkw 0x1f7d6b1ac0000000 0x23efad6358000000 0x1c7e739cc0000002 0x038fce7398000000

def z1090 : W := mkw 0x1ffdef7bc6020810 0x23ffbdef78c04102 0x1fffffffce000007 0xe3fffffff9c00000

def z1091 : W := mkw 0x219394e5701c71e5 0x0432729cae038e3c 0xa3b18c63f03cf3e5 0xf476318c7e079e7c

def z1092 : W := mkw 0xd3d1d47549f9e7ae 0x1a7a3a8ea93f3cf5 0x23c1f07c01f8e384 0x04783e0f803f1c70

def z1093 : W := mkw 0x20021084301c71e5 0x0400421086038e3c 0xa0018000303cf3e4 0xd400300006079e7c

def z1094 : W := mkw 0x1eec6f5a80000000 0x23dd8deb50000000 0x1fce73fc00000006 0x03f9ce7f80000000

def z1095 : W := mkw 0x56c00ed45b681f0a 0x0ad801da8b6d03e1 0xffc00ffcfff81f9f 0xbff801ff9fff03f3

def z1096 : W := mkw 0x2006b12f201c61e5 0x0400d625e4038c3c 0x204ff3ff003ce3e6 0xe409fe7fe0079c7c

def z1097 : W := mkw 0x0c2e0b82b6061850 0x0185c17056c0c30a 0xdc3e0c03fe071c79 0x5b87c1807fc0e38f

def z1098 : W := mkw 0x1ffdef7bc0c1860a 0x23ffbdef781830c1 0xffffffffc1c7ec1f 0xfffffffff838fd83

def z1099 : W := mkw 0x1ff9ce7140c1a6ae 0x03ff39ce281834d5 0xffffffffc1c7ffff 0xfffffffff838ffff

def z1100 : W := mkw 0x0c2e1b82b6165850 0x0185c37056c2cb0a 0xdc7e7f83fe3f1c7b 0xfb8fcff07fc7e38f

def z1101 : W := mkw 0xc00210843fffffae 0x1800421087fffff5 0xe00000003ffffff8 0x1c00000007ffffff

def z1102 : W := mkw 0x1ffdef7bc0c1860a 0x23ffbdef781830c1 0xdfffffffc1c71c7f 0xfbfffffff838e38f

def z1103 : W := mkw 0x2006318e301c5141 0x0400c631c6038a28 0xa04ff3fc303cf386 0xf409fe7f86079e70

def z1104 : W := mkw 0x0004a12bc0000000 0x2000942578000000 0x004ff3ffc0000006 0xe009fe7ff8000000

def z1105 : W := mkw 0x1e6c6b1a89200000 0x23cd8d6351240000 0xffce739c3ff80007 0x9ff9ce7387ff0000

def z1106 : W := mkw 0xa00210843d3e71e5 0x1400421087a7ce3c 0xa00000003e3cf3e0 0x1400000007c79e7c

def z1107 : W := mkw 0x9b7b50002db7c000 0x136f6a0005b6f800 0xbfcff0003ffce006 0xd7f9fe0007ff9c00

def z1108 : W := mkw 0x1ffdef7bc0000000 0x23ffbdef78000000 0x1fcffffc00000007 0xa3f9ffff80000000

def z1109 : W := mkw 0x0004a12b00c1a6ae 0x00009425601834d5 0xe04ff3ff01c7fffe 0xfc09fe7fe038ffff

def z1110 : W := mkw 0x56c4af7b0b600e00 0x0ad895ef616c01c0 0x5fcfffff0fc00c07 0xebf9ffffe1f80180

def z1111 : W := mkw 0x1ffdef7bc0000000 0x23ffbdef78000000 0x5fffffffc0030c1f 0xebfffffff8006183

def z1112 : W := mkw 0x0cacaf7bc0000000 0x219595ef78000000 0x1c7fffffc0000007 0xe38ffffff8000000

def z1113 : W := mkw 0x16c4af7b004026a4 0x02d895ef600804d4 0xffcfffff01c4ffe7 0xfff9ffffe0389ffc

def z1114 : W := mkw 0x00061186301c5140 0x0000c230c6038a28 0xa04ff3ff303cf3e6 0xf409fe7fe6079e7c

def z1115 : W := mkw 0x04000a0002000800 0x0080014000400100 0xdc300c03ce071c79 0xfb86018079c0e38f

def z1116 : W := mkw 0x200290a5361e79f5 0x04005214a6c3cf3e 0xe0318c63fe3ffffd 0xfc06318c7fc7ffff

def z1117 : W := mkw 0x56c00ed41b681f00 0x0ad801da836d03e0 0xffc00ffc3fff1fff 0xbff801ff87ffe3ff

def z1118 : W := mkw 0xa93ff12b6497e0ef 0x1527fe256c92fc1d 0x003ff003c007e078 0x4007fe007800fc0f

def z1119 : W := mkw 0x1ffdef7bc0c1a6ae 0x23ffbdef781834d5 0x3fffffffc1c7e3ff 0xe7fffffff838fc7f

def z1120 : W := mkw 0x9b7b50002db7c000 0x136f6a0005b6f800 0xfffff0033ffff067 0xfffffe0067fffe0c

def z1121 : W := mkw 0x1eecef7bc04026ae 0x23dd9def780804d5 0x1c4e7fffc0001ffa 0x2389cffff80003ff

def z1122 : W := mkw 0x1b7de12b0081a0a4 0x036fbc2560103414 0xfffff3ff01c7f3e7 0xfffffe7fe038fe7c

def z1123 : W := mkw 0x2c2e2b8eb60e1951 0x0585c571d6c1c32a 0xdc3e0f9ffe071c7b 0xfb87c1f3ffc0e38f

def z1124 : W := mkw 0x1a6ce12b00000000 0x034d9c2560000000 0x1c4ff3ff00000006 0xe389fe7fe0000000

def z1125 : W := mkw 0x1ffdef7bc4020010 0x23ffbdef78804002 0x1fffffffc003001f 0xe3fffffff8006003

def z1126 : W := mkw 0x0484af7bc0000000 0x209095ef78000000 0x000fffffc0000000 0x6001fffff8000000

def z1127 : W := mkw 0x0115a12b4081a0ae 0x0022b42568103415 0x007ff3ffc007e07e 0xe00ffe7ff800fc0f

def z1128 : W := mkw 0x20021084341e71e5 0x040042108683ce3c 0xe00000003e3ff3e0 0x1c00000007c7fe7c

def z1129 : W := mkw 0x1ffdef7bc081a0ae 0x23ffbdef78103415 0xbfffffffc007f3ff 0xf7fffffff800fe7f

def z1130 : W := mkw 0x1ffdef7bc9200000 0x23ffbdef79240000 0x3fffffffc1f80007 0xe7fffffff83f0000

def z1131 : W := mkw 0x9b7b50002db7c000 0x136f6a0005b6f800 0x3ffff0003fffe006 0x47fffe0007fffc00

def z1132 : W := mkw 0x2006b1af301c71e5 0x0400d635e6038e3c 0x204ff3ff003cf3e4 0x6409fe7fe0079e7c

def z1133 : W := mkw 0x9ffdef7bc4838000 0x33ffbdef78907000 0x1fffffffc0030007 0xe3fffffff8006000

def z1134 : W := mkw 0x1f794a1000000000 0x03ef294200000000 0x1ffff39c00000007 0xc3fffe7380000000

def z1135 : W := mkw 0x1b7b500029344000 0x036f6a0005268800 0xfffff0003ffce007 0xdffffe0007ff9c00

def z1136 : W := mkw 0xdffdef7bcfe38e00 0x3bffbdef79fc71c0 0x5fffffffcfc30c07 0xebfffffff9f86180

def z1137 : W := mkw 0x0004210a00000000 0x0000842140000000 0x004e739f00000002 0xe009ce73e0000000

def z1138 : W := mkw 0x0c2e0b82b6061850 0x0185c17056c0c30a 0x1c3e0f83fe071c7a 0x6387c1f07fc0e38f

def z1139 : W := mkw 0x56c00ed41b681f00 0x0ad801da836d03e0 0xffc00ffffff81fff 0xbff801ffffff03ff

def z1140 : W := mkw 0x0004a12b00000000 0x0000942560000000 0x004e73ff00000002 0x2009ce7fe0000000

def z1141 : W := mkw 0x0004a12b000020a4 0x0000942560000414 0x004ff3ff000013e6 0xe009fe7fe000027c

def z1142 : W := mkw 0x1ffdef7bc9200000 0x23ffbdef79240000 0x5fffffffcfc00007 0xebfffffff9f80000

def z1143 : W := mkw 0x1e6ceb3bc0000000 0x23cd9d6778000000 0x1c4e739fc0000002 0x0389ce73f8000000

def z1144 : W := mkw 0x56c00ed41b681f00 0x0ad801da836d03e0 0xfff00ffc3fff1f87 0xfffe01ff87ffe3f0

def z1145 : W := mkw 0x20021084301c71e5 0x0400421086038e3c 0x00000000303ce060 0x0000000006079c0c

def z1146 : W := mkw 0x0004a12b00000000 0x0000942560000000 0xa04ff3ff0004e006 0xf409fe7fe0009c00

def z1147 : W := mkw 0x1244611a00000000 0x22488c2340000000 0x004e739c00000002 0x0009ce7380000000

def z1148 : W := mkw 0x608294e53b7c7fe5 0x0c10529ca76f8ffc 0xe3818c633ffcffe5 0xfc70318c67ff9ffc

def z1149 : W := mkw 0x0191846140c1a6ae 0x0032308c281834d5 0xe3b18c03c1c7fff9 0x5c7631807838ffff

def z1150 : W := mkw 0x1ffdef7bc6c38e1a 0x23ffbdef78d871c3 0x5fffffffcfc30c1f 0xebfffffff9f86183

def z1151 : W := mkw 0xa00210843d3e5141 0x1400421087a7ca28 0x000000003e380000 0x0000000007c70000

def z1152 : W := mkw 0x6484afff52483fef 0x0c9095ffea4907fd 0x00000fffc0001ff8 0x200001fff80003ff

def z1153 : W := mkw 0x0c2c0b8296021850 0x0185817052c0430a 0xdc300f83ce071c79 0xfb8601f079c0e38f

def z1154 : W := mkw 0x1e6c6b1a80000000 0x23cd8d6350000000 0x1c4e739f00000002 0xe389ce73e0000000

def z1155 : W := mkw 0x9b7b50002db7c000 0x136f6a0005b6f800 0xfffff0003ffffc7f 0xdffffe0007ffff8f

def z1156 : W := mkw 0x1ffdef7bc0818000 0x23ffbdef78103000 0xffffffffc1c7fc7f 0xfffffffff838ff8f

def z1157 : W := mkw 0x0006b1af301c5100 0x0000d635e6038a20 0xa04ff3ff303cf386 0xf409fe7fe6079e70

def z1158 : W := mkw 0x1eec6f5a80400600 0x23dd8deb500800c0 0xffce7ffc01c01f87 0xbff9cfff803803f0

def z1159 : W := mkw 0x000290a5301c71a4 0x00005214a6038e34 0xa04ff3ff303cf3e6 0xf409fe7fe6079e7c

def z1160 : W := mkw 0x1ffd6f5ac0000000 0x23ffadeb58000000 0x1fffff9cc0000007 0xc3fffff398000000

def z1161 : W := mkw 0x20021084305c77ef 0x04004210860b8efd 0xa0000000303cfff8 0x1400000006079fff

def z1162 : W := mkw 0x1ffdef7bc0c1a6ae 0x23ffbdef781834d5 0x3fffffffc1c0ffff 0xe7fffffff8381fff

def z1163 : W := mkw 0x524000841b681f00 0x0a480010836d03e0 0xffc003fc3ff81f87 0xbff8007f87ff03f0

def z1164 : W := mkw 0x1ffdef7bc04026ae 0x23ffbdef780804d5 0xdfffffffc0071fff 0xfbfffffff800e3ff

def z1165 : W := mkw 0x20021084309df1e5 0x040042108613be3c 0xe000000031fff3e0 0x1c000000063ffe7c

def z1166 : W := mkw 0x9b7b50002db7c000 0x136f6a0005b6f800 0xfffff003ffffe07f 0xdffffe007ffffc0f

def z1167 : W := mkw 0x20021084301c5141 0x0400421086038a28 0xa0000000303ce000 0x1400000006079c00

def z1168 : W := mkw 0x0115e12b40000000 0x2022bc2568000000 0x004ff3ff00000006 0xe009fe7fe0000000

def z1169 : W := mkw 0x17d5af7b40c1a6ae 0x02fab5ef681834d5 0xffffffffc1c7ffff 0xfffffffff838ffff

def z1170 : W := mkw 0x1ffdef7b00000000 0x03ffbdef60000000 0x1fffffff00000007 0xe3ffffffe0000000

def z1171 : W := mkw 0x20021084301c5141 0x0400421086038a28 0x80000000303c1060 0x100000000607820c

def z1172 : W := mkw 0x0111000000c1a6ae 0x00222000001834d5 0xe3b18c03c1c7fffd 0xfc7631807838ffff

def z1173 : W := mkw 0x1ff94e50c0000000 0x23ff29ca18000000 0x1ffffffcc0000007 0xe3ffffff98000000

def z1174 : W := mkw 0x293fb12be497e0ff 0x0527f6257c92fc1f 0x003ff003c007e078 0x4007fe007800fc0f

def z1175 : W := mkw 0x5ffdef7bcf620e10 0x2bffbdef79ec41c2 0x5fffffffcfc30c1f 0xebfffffff9f86183

def z1176 : W := mkw 0x1ffdef7bc04026ae 0x23ffbdef780804d5 0x1fffffffc0000387 0xe3fffffff8000070

def z1177 : W := mkw 0x0191846140c1a6ae 0x0032308c281834d5 0xffb18c63ffc7ffff 0xfff6318c7ff8ffff

def z1178 : W := mkw 0x0c2e0b82b6061850 0x0185c17056c0c30a 0xfc3e0fe3fe071fff 0xff87c1fc7fc0e3ff

def z1179 : W := mkw 0x0c280a8096021810 0x0185015012c04302 0xdc300f83fe071c7b 0xfb8601f07fc0e38f

def z1180 : W := mkw 0x20021084321c79e5 0x0400421086438f3c 0xe00000003e3cffe0 0x1c00000007c79ffc

def z1181 : W := mkw 0x1e6c6b1a80000000 0x23cd8d6350000000 0xdc7e7f9fc0071c7b 0xfb8fcff3f800e38f

def z1182 : W := mkw 0x0c2e0b86b60e1950 0x0185c170d6c1c32a 0xdc3e0ffffe071ffb 0xfb87c1ffffc0e3ff

def z1183 : W := mkw 0x2004a12b000020e5 0x040094256000041c 0x004ff3ff00000066 0xe009fe7fe000000c

def z1184 : W := mkw 0x0c2e0b02a6060850 0x0185c16054c0c10a 0xdc3e0c03ce071c79 0xfb87c18079c0e38f

def z1185 : W := mkw 0x0004a12b00000000 0x0000942560000000 0x804ff3ff00041066 0xf009fe7fe000820c

def z1186 : W := mkw 0x9b7b50002db7c000 0x136f6a0005b6f800 0xffcff0003ff8e007 0x9ff9fe0007ff1c00

def z1187 : W := mkw 0x600210843b7c5f41 0x0c004210876f8be8 0xe00000003ff81f80 0x1c00000007ff03f0

def z1188 : W := mkw 0x1ffdef7bc0000000 0x23ffbdef78000000 0x03ffffffc0000004 0x607ffffff8000000

def z1189 : W := mkw 0x1bfde56b40c1a6ae 0x037fbcad681834d5 0xffffffffc1c7ffff 0xfffffffff838ffff

def z1190 : W := mkw 0x208294e5705c77ef 0x0410529cae0b8efd 0xa0000c63f03cfff8 0x3400018c7e079fff

def z1191 : W := mkw 0x082e0102a4060050 0x0105c0205480c00a 0xdc3e0c03fe071c7b 0xfb87c1807fc0e38f

def z1192 : W := mkw 0x1ee84e5000000000 0x03dd09ca00000000 0x1fce7ffc00000007 0xa3f9cfff80000000

def z1193 : W := mkw 0x56c00ed41b681f50 0x0ad801da836d03ea 0xffc00ffc3ff81fff 0xbff801ff87ff03ff

def z1194 : W := mkw 0x0191044000c18600 0x00322088001830c0 0xe3b18c63c1c7fffd 0xfc76318c7838ffff

def z1195 : W := mkw 0x2006b1af301c71e5 0x0400d635e6038e3c 0xa04ff3fc303cf3e6 0x1409fe7f86079e7c

def z1196 : W := mkw 0x011180210081a0a4 0x0022300420103414 0xe3b18c63c1c7fffd 0xfc76318c7838ffff

def z1197 : W := mkw 0x76c21ed43b7c7fe5 0x0ed843da876f8ffc 0xff800c003ffcffe1 0x1ff0018007ff9ffc

def z1198 : W := mkw 0x1ffdef7bc0400600 0x23ffbdef780800c0 0x5fffffffc1c00c07 0xebfffffff8380180

def z1199 : W := mkw 0x1e6c6b1a80000000 0x23cd8d6350000000 0x1c7e739c00000003 0xc38fce7380000000

def z1200 : W := mkw 0x1f7deb3b80000000 0x23efbd6770000000 0x1ffff3ff00000007 0xe3fffe7fe0000000

def z1201 : W := mkw 0x9b7de12b0da38000 0x136fbc2561b47000 0x5ffff3ff0fc30007 0xebfffe7fe1f86000

def z1202 : W := mkw 0x0115a12b40000000 0x0022b42568000000 0x007ff3ffc0000006 0xe00ffe7ff8000000

def z1203 : W := mkw 0x1f7deb3bc0000000 0x23efbd6778000000 0x1c4ff39c00000002 0x0389fe7380000000

def z1204 : W := mkw 0x0dbdef7bc0000000 0x21b7bdef78000000 0x007fffffc0000006 0xe00ffffff8000000

def z1205 : W := mkw 0x1ffdef7bc00020a4 0x23ffbdef78000414 0xffffffffc007ffff 0xfffffffff800ffff

def z1206 : W := mkw 0x20021084361e5951 0x0400421086c3cb2a 0x000000003e380000 0x0000000007c70000

def z1207 : W := mkw 0x0c2a0a00a6060810 0x0185414014c0c102 0xdc3e0c03fe071c7b 0xfb87c1807fc0e38f

def z1208 : W := mkw 0x9b7b50002db7c000 0x136f6a0005b6f800 0x7ffff0003ffbe007 0x0ffffe0007ff7c00

def z1209 : W := mkw 0x1244e13b00000000 0x22489c2760000000 0x004ff3ff00000006 0xe009fe7fe0000000

def z1210 : W := mkw 0x1e6ceb3b80000000 0x23cd9d6770000000 0x1c7fffffc0000007 0xe38ffffff8000000

def z1211 : W := mkw 0x1ffdef7bc081a0ae 0x23ffbdef78103415 0x1fffffffc000e007 0xe3fffffff8001c00

def z1212 : W := mkw 0x1e6c6b1a80000000 0x23cd8d6350000000 0x1c4e7f9c00000003 0xa389cff380000000

def z1213 : W := mkw 0x082ca12b00000000 0x0105942560000000 0x1c7ff3ff00000007 0xe38ffe7fe0000000

def z1214 : W := mkw 0x600210843f7e7ff5 0x0c00421087efcffe 0xe00000003ffffff8 0x1c00000007ffffff

def z1215 : W := mkw 0xdff94e508fe38e10 0x1bff29ca11fc71c2 0x5fb00c00cfc30c19 0x0bf6018019f86183

def z1216 : W := mkw 0x1ffdef7bc00020a4 0x23ffbdef78000414 0x3fffffffc000e387 0xe7fffffff8001c70

def z1217 : W := mkw 0x1ffdef7bc0000050 0x23ffbdef7800000a 0x1fffffffc000007f 0xe3fffffff800000f

def z1218 : W := mkw 0x1e6c6b1a80000000 0x23cd8d6350000000 0x1fce739c00000007 0x83f9ce7380000000

def z1219 : W := mkw 0x1ffdef7bc00020a4 0x23ffbdef78000414 0x1fffffffc00013e7 0xe3fffffff800027c

def z1220 : W := mkw 0x1ffdef7bc9e1a6ae 0x23ffbdef793c34d5 0xffffffffffffffff 0xffffffffffffffff

def z1221 : W := mkw 0x1b7d610a00000000 0x036fac2140000000 0x1ffff39c00000007 0xc3fffe7380000000

def z1222 : W := mkw 0x1bfde57bc0000000 0x237fbcaf78000000 0x03fff3ffc0000006 0xe07ffe7ff8000000

def z1223 : W := mkw 0x1ffdef7bc0400600 0x23ffbdef780800c0 0xffffffffc1c71fff 0xfffffffff838e3ff

def z1224 : W := mkw 0x2006b1afb01c71f5 0x0400d635f6038e3e 0xa04ff3fff03cf3fe 0xf409fe7ffe079e7f

def z1225 : W := mkw 0xc00210843fbfd900 0x1800421087f7fb20 0xe00000003fffe000 0x1c00000007fffc00

def z1226 : W := mkw 0xa00210843fbff9f5 0x1400421087f7ff3e 0xe00000003ffffff8 0x1c00000007ffffff

def z1227 : W := mkw 0x9b7b50002db7c000 0x136f6a0005b6f800 0x5ffff0003fffe003 0x4bfffe0007fffc00

def z1228 : W := mkw 0x1244a12b09200000 0x0248942561240000 0xffcff3ff3ff80007 0xfff9fe7fe7ff0000

def z1229 : W := mkw 0x0c2e0b82b6061850 0x0185c17056c0c30a 0x5c3e0f83ce071c79 0x6b87c1f079c0e38f

def z1230 : W := mkw 0x1e6c6b1a80000000 0x23cd8d6350000000 0x1c4ff39c00000006 0xc389fe7380000000

def z1231 : W := mkw 0x0c2cab2b80000000 0x0185956570000000 0x1c4ff3ff00000006 0xe389fe7fe0000000

def z1232 : W := mkw 0x1ffdef7bc0c1860a 0x23ffbdef781830c1 0x1fffffffc1c00007 0xe3fffffff8380000

def z1233 : W := mkw 0x200290a5301c71e5 0x04005214a6038e3c 0xa0000063303cf3e0 0x3400000c66079e7c

def z1234 : W := mkw 0x20021084309df1ef 0x040042108613be3d 0xa0000000303ff3f8 0x140000000607fe7f

def z1235 : W := mkw 0x2004b1af101871a5 0x04009635e2030e34 0xa04ff3ff3038f386 0xf409fe7fe6071e70

def z1236 : W := mkw 0x0115a12b00000000 0x0022b42560000000 0x03fff3ff00000007 0xe07ffe7fe0000000

def z1237 : W := mkw 0x0084a56b00000000 0x001094ad60000000 0x03cfffff00000007 0xe079ffffe0000000

def z1238 : W := mkw 0x56c00ed41b681f00 0x0ad801da836d03e0 0xffc003fc3ff80387 0x9ff8007f87ff0070

def z1239 : W := mkw 0x1ffdef7bc0400600 0x23ffbdef780800c0 0x3fffffffc1c00387 0xe7fffffff8380070

def z1240 : W := mkw 0x09bde56bc0000000 0x2137bcad78000000 0x03ffffffc0000007 0xe07ffffff8000000

def z1241 : W := mkw 0x0dbdef7bc0000000 0x21b7bdef78000000 0x03bfffffc0000005 0xe077fffff8000000

def z1242 : W := mkw 0x1b79400000000000 0x036f280000000000 0x1ffff3fc00000007 0xe3fffe7f80000000

def z1243 : W := mkw 0x082ca12b80000000 0x0105942570000000 0x007ff3ffc0000006 0xe00ffe7ff8000000

def z1244 : W := mkw 0x0191846140c1a6ae 0x0032308c281834d5 0x43b18c63c1c7fff9 0x6876318c7838ffff

def z1245 : W := mkw 0x1ffdef7bc6c3aebe 0x23ffbdef78d875d7 0xffffffffcfc7ffff 0xfffffffff9f8ffff

def z1246 : W := mkw 0x2006b1af301c71e5 0x0400d635e6038e3c 0x204ff3ff3038f3e6 0x2409fe7fe6071e7c

def z1247 : W := mkw 0xa93ff12ba497e0f5 0x1527fe257492fc1e 0x003ff003c007e078 0x4007fe007800fc0f

def z1248 : W := mkw 0x5ffdef7bc2400e00 0x2bffbdef784801c0 0x1fffffffc0000c07 0xe3fffffff8000180

def z1249 : W := mkw 0x0004a12b00000000 0x0000942560000000 0xa04ff3ff30380006 0xf409fe7fe6070000

def z1250 : W := mkw 0x0c2e0b82b6061850 0x0185c17056c0c30a 0xfc3f8f83fe07fc7f 0xff87f1f07fc0ff8f

def z1251 : W := mkw 0x9b7b50006db7c00a 0x136f6a000db6f801 0xfffff000ffffe01f 0xdffffe001ffffc03

def z1252 : W := mkw 0x13d5e57b40000000 0x227abcaf68000000 0x03ffffffc0000007 0xe07ffffff8000000

def z1253 : W := mkw 0x0dbdef7bc0c1a6ae 0x21b7bdef781834d5 0x003fffffc007fff8 0x6007fffff800ffff

def z1254 : W := mkw 0x1bfde57b40000000 0x237fbcaf68000000 0x1ffff3ff00000007 0xe3fffe7fe0000000

def z1255 : W := mkw 0x1eecef7bc0000000 0x23dd9def78000000 0x1c4e73fc00000002 0x0389ce7f80000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z7,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z8,z6]),(0,[z9,z0,z1,z2,z4,z5,z6])],[(0,[z10,z0,z1,z2,z4,z5,z6]),(0,[z11,z0,z12,z2,z4,z5,z6]),(0,[z0,z1,z13,z4,z5,z14,z6]),(0,[z0,z15,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z16]),(0,[z0,z1,z2,z4,z17,z5,z6])],[(0,[z18,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z13,z2,z4,z19,z6]),(0,[z0,z1,z2,z20,z4,z5,z6])],[(0,[z0,z1,z21,z22,z4,z5,z6]),(0,[z0,z23,z1,z22,z4,z5,z6]),(1,[z0,z1,z24,z4,z5,z6]),(0,[z25,z0,z1,z4,z5,z6,z26])],[(0,[z0,z1,z22,z4,z5,z6,z27]),(0,[z28,z0,z1,z21,z4,z5,z6]),(0,[z0,z1,z2,z4,z29,z30,z6]),(0,[z28,z0,z1,z31,z4,z5,z6]),(0,[z32,z0,z1,z33,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z34,z6]),(0,[z0,z1,z35,z2,z4,z5,z6]),(0,[z0,z1,z2,z5,z6,z36,z37])],[(0,[z0,z1,z2,z38,z4,z5,z6]),(0,[z0,z1,z24,z4,z39,z5,z6]),(0,[z0,z40,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z41])],[(0,[z0,z1,z42,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z43]),(0,[z0,z1,z2,z44,z4,z5,z6]),(0,[z0,z1,z45,z4,z5,z6,z46]),(0,[z0,z1,z2,z4,z5,z6,z47]),(0,[z0,z1,z2,z4,z48,z5,z6])],[(0,[z0,z1,z49,z22,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z50]),(0,[z0,z1,z2,z4,z5,z51,z6]),(0,[z0,z1,z2,z4,z52,z5,z6]),(0,[z0,z1,z4,z19,z5,z14,z6]),(0,[z0,z1,z4,z5,z14,z6,z46]),(0,[z53,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z54,z6]),(0,[z0,z1,z2,z4,z5,z55,z6])]],
   [[(0,[z0,z1,z56,z22,z4,z5,z6]),(0,[z57,z0,z1,z2,z58,z5,z6]),(0,[z1,z2,z4,z30,z5,z59,z6]),(0,[z60,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z61,z2,z4,z5,z6])],[(0,[z0,z1,z62,z2,z4,z5,z6]),(0,[z0,z1,z2,z63,z4,z5,z6]),(0,[z0,z64,z1,z2,z4,z5,z6]),(0,[z65,z0,z1,z2,z4,z5,z6]),(0,[z0,z66,z1,z33,z4,z5,z6]),(0,[z0,z1,z2,z4,z67,z5,z6]),(0,[z0,z1,z2,z4,z5,z68,z6])],[(0,[z0,z1,z21,z4,z5,z6,z37]),(0,[z0,z2,z69,z4,z39,z5,z6])],[(0,[z11,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z70,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z71,z6]),(0,[z0,z1,z2,z4,z72,z5,z6]),(0,[z0,z1,z33,z4,z5,z14,z6]),(0,[z0,z1,z2,z73,z4,z5,z6])],[(0,[z0,z74,z1,z22,z4,z5,z6]),(0,[z0,z1,z75,z2,z4,z5,z6]),(0,[z0,z76,z1,z2,z4,z5,z6]),(0,[z0,z77,z1,z13,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z78,z6]),(0,[z0,z1,z2,z79,z80,z5,z6]),(0,[z0,z1,z2,z4,z5,z81,z6]),(0,[z0,z1,z82,z2,z4,z5,z6])],[(0,[z0,z1,z22,z4,z29,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z6]),(0,[z0,z1,z2,z4,z5,z83,z6])],[(0,[z0,z1,z22,z4,z84,z5,z6]),(0,[z0,z85,z1,z2,z4,z5,z6]),(0,[z25,z0,z1,z69,z4,z5,z6]),(0,[z0,z1,z2,z86,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z87,z6]),(0,[z0,z1,z88,z2,z4,z5,z54])],[(0,[z0,z1,z21,z4,z5,z34,z6]),(0,[z89,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z90,z2,z91,z5,z6]),(0,[z0,z92,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z93])]],
   [[(0,[z94,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z22,z4,z5,z6]),(0,[z0,z1,z22,z95,z4,z5,z6]),(0,[z57,z0,z1,z2,z84,z5,z6]),(0,[z25,z96,z0,z1,z4,z5,z6]),(0,[z97,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z98,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z99,z6]),(0,[z0,z1,z21,z4,z48,z5,z6]),(0,[z0,z100,z1,z4,z84,z5,z6]),(0,[z0,z1,z101,z2,z4,z5,z6]),(0,[z0,z1,z102,z2,z4,z5,z6]),(1,[z0,z103,z2,z4,z5,z26]),(0,[z0,z1,z104,z33,z4,z5,z6]),(0,[z0,z1,z2,z4,z105,z5,z6])],[(0,[z0,z1,z2,z4,z5,z106,z6]),(0,[z0,z1,z22,z4,z5,z107,z6]),(0,[z0,z1,z21,z4,z5,z54,z6]),(0,[z108,z0,z1,z2,z69,z5,z6]),(0,[z0,z1,z44,z33,z4,z5,z6]),(0,[z109,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z22,z4,z5,z6,z26]),(0,[z0,z1,z2,z110,z4,z5,z6]),(0,[z0,z1,z2,z4,z29,z59,z6]),(0,[z0,z1,z2,z4,z111,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z112])],[(0,[z0,z113,z1,z2,z4,z5,z6]),(0,[z25,z0,z1,z22,z4,z5,z6]),(0,[z0,z1,z21,z4,z30,z5,z6]),(0,[z114,z0,z1,z2,z58,z5,z6]),(0,[z0,z23,z2,z4,z5,z115,z6]),(0,[z116,z0,z1,z33,z4,z5,z6]),(0,[z0,z1,z33,z4,z5,z6,z117]),(0,[z0,z1,z33,z118,z4,z5,z6]),(0,[z119,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z120,z2,z4,z5,z6]),(0,[z0,z1,z104,z121,z4,z5,z6])],[(0,[z0,z122,z1,z2,z4,z5,z6]),(0,[z123,z1,z2,z4,z5,z59,z6]),(0,[z0,z1,z2,z4,z5,z6,z124]),(1,[z96,z1,z2,z4,z30,z6]),(0,[z125,z0,z1,z2,z4,z5,z6])],[(0,[z25,z0,z1,z126,z4,z5,z6]),(0,[z127,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z80,z5,z81,z6]),(0,[z0,z1,z2,z4,z128,z5,z6])],[(0,[z0,z1,z2,z4,z129,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z130]),(0,[z0,z131,z1,z2,z4,z5,z6])]],
   [[(1,[z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z33,z58,z4,z5,z6]),(1,[z0,z1,z70,z4,z5,z6]),(0,[z0,z23,z1,z2,z4,z5,z115]),(0,[z132,z0,z1,z33,z4,z5,z6]),(0,[z0,z74,z1,z4,z5,z34,z6])],[(0,[z0,z1,z104,z21,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z133,z6])],[(0,[z0,z1,z22,z4,z5,z6,z46]),(0,[z123,z96,z1,z2,z4,z5,z6]),(0,[z0,z1,z134,z2,z4,z5,z6])],[(0,[z0,z1,z135,z2,z4,z5,z6]),(0,[z25,z136,z0,z1,z4,z5,z6]),(0,[z25,z0,z1,z4,z5,z6,z37]),(0,[z0,z1,z2,z137,z4,z5,z6])],[(0,[z138,z0,z103,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z139,z6]),(0,[z0,z140,z2,z58,z4,z5,z6]),(0,[z123,z0,z1,z101,z4,z5,z6]),(0,[z0,z1,z2,z33,z4,z5,z6])],[(0,[z0,z1,z141,z33,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z142])],[(0,[z143,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z22,z69,z4,z5,z6]),(0,[z0,z1,z144,z2,z4,z5,z6])],[(0,[z0,z1,z145,z2,z4,z5,z6]),(0,[z0,z1,z2,z146,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z147,z6])]],
   [[(0,[z148,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z149,z6]),(0,[z150,z0,z1,z2,z4,z5,z6]),(0,[z25,z0,z1,z4,z5,z34,z6])],[(0,[z0,z1,z2,z4,z5,z151,z6]),(0,[z138,z0,z1,z21,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z152]),(0,[z0,z1,z2,z4,z5,z153,z6]),(0,[z0,z154,z1,z2,z4,z5,z6]),(0,[z0,z155,z1,z2,z4,z5,z6]),(1,[z0,z156,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z157,z6])],[(0,[z158,z0,z1,z2,z4,z5,z6]),(0,[z57,z0,z1,z21,z4,z5,z6]),(0,[z0,z140,z1,z2,z4,z5,z6]),(0,[z25,z0,z1,z4,z48,z5,z6]),(0,[z0,z1,z13,z2,z4,z5,z6]),(0,[z159,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z118,z5,z81])],[(1,[z158,z0,z1,z4,z5,z6]),(1,[z160,z1,z21,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z161]),(0,[z0,z1,z2,z162,z4,z5,z6]),(0,[z25,z0,z1,z4,z5,z54,z6]),(0,[z0,z1,z33,z4,z5,z163,z6])],[(0,[z0,z1,z22,z22,z4,z5,z6]),(1,[z0,z140,z2,z4,z5,z6]),(0,[z0,z1,z2,z31,z4,z5,z6]),(0,[z108,z0,z2,z4,z39,z5,z6]),(0,[z25,z0,z12,z1,z4,z5,z6]),(0,[z25,z0,z164,z1,z4,z5,z6])],[(0,[z0,z2,z4,z39,z5,z6,z26]),(0,[z0,z165,z1,z2,z4,z5,z6])],[(0,[z0,z1,z166,z21,z4,z5,z6]),(0,[z167,z0,z1,z2,z4,z5,z6]),(0,[z168,z0,z1,z22,z4,z5,z6]),(0,[z169,z0,z1,z21,z4,z5,z6]),(0,[z0,z77,z1,z21,z4,z5,z6]),(0,[z0,z1,z33,z4,z29,z5,z6]),(0,[z25,z0,z1,z13,z4,z5,z6]),(0,[z0,z170,z1,z2,z4,z5,z6])],[(0,[z0,z1,z22,z4,z171,z5,z6]),(0,[z0,z1,z21,z33,z4,z5,z6]),(0,[z0,z1,z33,z4,z84,z5,z6]),(0,[z123,z0,z1,z2,z4,z5,z6]),(0,[z0,z23,z1,z33,z4,z5,z6]),(0,[z0,z1,z172,z2,z4,z5,z6])]],
   [[(0,[z25,z0,z1,z4,z5,z81,z6]),(1,[z0,z1,z104,z2,z4,z37])],[(0,[z138,z0,z1,z2,z173,z5,z6]),(0,[z108,z0,z1,z21,z4,z5,z6]),(0,[z0,z1,z174,z21,z4,z5,z6]),(0,[z0,z1,z2,z175,z4,z5,z6])],[(0,[z0,z0,z1,z2,z4,z5,z6]),(0,[z11,z0,z103,z2,z4,z5,z6]),(0,[z0,z1,z90,z22,z4,z5,z6]),(0,[z0,z1,z2,z4,z176,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z177]),(0,[z0,z1,z45,z4,z19,z5,z6]),(0,[z0,z1,z178,z2,z4,z5,z6])],[(0,[z0,z1,z22,z4,z5,z179,z6]),(0,[z0,z1,z22,z4,z5,z6,z37]),(0,[z0,z1,z2,z4,z5,z6,z180]),(0,[z0,z1,z2,z4,z5,z181,z6]),(0,[z25,z0,z1,z4,z5,z182,z6]),(0,[z183,z0,z1,z2,z4,z5,z6])],[(0,[z0,z184,z1,z2,z4,z5,z6]),(1,[z168,z1,z2,z4,z5,z185]),(0,[z0,z1,z186,z2,z4,z5,z6]),(1,[z0,z1,z120,z2,z4,z6]),(0,[z187,z0,z1,z2,z5,z6,z37])],[(0,[z0,z188,z1,z22,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z189,z6]),(0,[z190,z0,z1,z2,z4,z5,z6])],[(0,[z114,z0,z1,z21,z4,z5,z6])],[(0,[z11,z0,z1,z21,z4,z5,z6]),(0,[z0,z191,z1,z21,z4,z5,z6]),(0,[z0,z1,z2,z4,z192,z5,z6]),(0,[z0,z1,z2,z4,z193,z5,z6]),(0,[z194,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z195,z5,z6])]],
   [[(0,[z0,z1,z22,z4,z5,z34,z6]),(0,[z0,z1,z21,z79,z4,z5,z6]),(0,[z0,z74,z1,z33,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z196])],[(0,[z0,z1,z2,z4,z4,z5,z6]),(1,[z0,z2,z4,z197,z5,z6]),(0,[z0,z1,z2,z4,z198,z5,z6]),(0,[z199,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z200,z5,z6]),(0,[z0,z1,z2,z4,z201,z5,z6]),(0,[z0,z1,z2,z4,z5,z202,z6]),(0,[z25,z0,z1,z203,z4,z5,z6]),(0,[z0,z1,z2,z4,z204,z5,z6]),(0,[z0,z1,z2,z4,z5,z205,z6]),(0,[z0,z1,z2,z4,z5,z6,z206]),(0,[z0,z1,z2,z4,z48,z5,z207]),(0,[z0,z1,z2,z4,z5,z6,z208])],[(0,[z0,z1,z22,z4,z5,z54,z6]),(0,[z209,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z210,z6]),(0,[z0,z1,z2,z211,z4,z5,z6]),(0,[z132,z25,z0,z1,z4,z5,z6]),(0,[z212,z25,z0,z1,z4,z5,z6]),(0,[z0,z1,z33,z4,z5,z6,z46]),(0,[z109,z0,z1,z2,z4,z54,z6])],[(0,[z0,z1,z213,z2,z4,z5,z6]),(0,[z214,z0,z1,z22,z4,z5,z6]),(0,[z160,z0,z1,z22,z4,z5,z6]),(0,[z0,z215,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z59,z216,z6]),(0,[z0,z164,z2,z4,z39,z5,z6]),(1,[z0,z1,z33,z4,z5,z6]),(0,[z32,z0,z156,z2,z4,z5,z6])],[(0,[z0,z217,z1,z2,z4,z5,z6]),(0,[z0,z1,z22,z4,z30,z5,z6])],[(0,[z138,z0,z12,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z218,z6]),(0,[z0,z219,z1,z2,z4,z5,z6])],[(0,[z138,z11,z1,z2,z4,z5,z6]),(0,[z0,z220,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z221,z1,z22,z4,z5,z6]),(0,[z0,z1,z2,z222,z4,z5,z6]),(0,[z0,z1,z223,z2,z4,z5,z6]),(0,[z0,z224,z1,z2,z4,z5,z6]),(0,[z25,z0,z1,z33,z4,z5,z6])],[(0,[z0,z164,z1,z21,z4,z5,z6]),(0,[z0,z1,z225,z2,z4,z5,z6]),(0,[z168,z0,z1,z226,z4,z5,z6]),(0,[z0,z1,z2,z4,z227,z5,z6]),(0,[z0,z1,z228,z2,z4,z5,z6])],[(0,[z96,z0,z1,z22,z4,z5,z6]),(0,[z0,z1,z33,z4,z5,z185,z6]),(0,[z0,z1,z2,z4,z229,z5,z6]),(0,[z0,z1,z2,z4,z5,z230,z6])],[(0,[z0,z231,z1,z2,z4,z5,z6]),(0,[z0,z232,z1,z33,z4,z5,z6]),(0,[z0,z1,z233,z104,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z234]),(0,[z0,z1,z2,z235,z4,z5,z6])],[(1,[z0,z1,z21,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z236]),(1,[z0,z1,z2,z237,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z238]),(0,[z0,z1,z2,z4,z239,z5,z6]),(0,[z0,z1,z240,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z48,z207])],[(0,[z0,z1,z2,z241,z4,z5,z6]),(0,[z0,z1,z21,z4,z5,z6,z206]),(0,[z0,z1,z2,z242,z4,z5,z6]),(0,[z0,z66,z1,z2,z69,z5,z6]),(0,[z243,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z244,z6])],[(0,[z245,z0,z1,z22,z4,z5,z6]),(0,[z0,z1,z22,z4,z246,z5,z6]),(0,[z25,z0,z23,z1,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z247,z6]),(0,[z0,z1,z2,z4,z5,z6,z248])],[(0,[z0,z249,z1,z2,z4,z5,z6]),(0,[z0,z1,z4,z5,z34,z6,z46]),(0,[z0,z1,z2,z4,z5,z6,z250])]],
   [[(0,[z0,z1,z2,z4,z5,z115,z27]),(0,[z25,z0,z1,z31,z4,z5,z6]),(0,[z251,z0,z1,z33,z4,z5,z6]),(1,[z0,z1,z13,z4,z34,z6]),(0,[z0,z1,z13,z2,z4,z34,z6]),(0,[z252,z0,z1,z2,z4,z5,z6]),(0,[z0,z253,z1,z4,z80,z5,z6])],[(0,[z0,z254,z1,z2,z4,z5,z6]),(1,[z11,z184,z2,z4,z5,z6]),(0,[z0,z1,z203,z21,z4,z5,z6]),(0,[z0,z1,z2,z255,z4,z5,z6]),(0,[z28,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z256,z6]),(0,[z0,z257,z1,z2,z4,z5,z6]),(1,[z0,z258,z2,z4,z5,z6])],[(0,[z0,z259,z1,z2,z4,z5,z6]),(0,[z0,z1,z260,z2,z4,z5,z6]),(1,[z136,z1,z2,z4,z5,z27]),(0,[z0,z1,z33,z4,z261,z5,z6]),(0,[z0,z1,z2,z4,z262,z5,z6]),(0,[z0,z1,z2,z4,z5,z263,z6])],[(0,[z0,z103,z1,z21,z4,z5,z6]),(0,[z0,z1,z2,z4,z264,z5,z6]),(0,[z0,z77,z1,z2,z4,z19,z6])],[(0,[z0,z1,z2,z84,z39,z5,z6]),(0,[z265,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z266,z4,z5,z6])],[(0,[z267,z0,z1,z2,z4,z5,z6]),(0,[z0,z12,z1,z2,z4,z29,z6])],[(0,[z0,z1,z2,z79,z4,z54,z6])],[(0,[z268,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z260,z4,z5,z6]),(0,[z0,z66,z2,z4,z5,z216,z6]),(0,[z0,z1,z2,z4,z5,z269,z6]),(0,[z270,z0,z1,z33,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z271])]],
   [[(0,[z0,z1,z22,z33,z4,z5,z6]),(0,[z0,z1,z222,z4,z84,z5,z6]),(0,[z272,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z226,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z273,z5,z6]),(0,[z0,z1,z274,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z115,z6,z26]),(0,[z275,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z104,z2,z4,z5,z37])],[(0,[z276,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z277,z6]),(0,[z0,z1,z2,z4,z278,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z279]),(1,[z25,z0,z1,z33,z5,z6])],[(0,[z280,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z281,z5,z6]),(0,[z0,z2,z58,z4,z197,z5,z6]),(0,[z168,z0,z1,z33,z4,z5,z6]),(0,[z282,z0,z1,z2,z4,z5,z6]),(0,[z283,z0,z1,z2,z4,z5,z6]),(0,[z284,z0,z1,z2,z4,z5,z6])],[(0,[z138,z0,z1,z2,z4,z5,z285]),(0,[z286,z0,z1,z2,z4,z5,z6]),(0,[z0,z287,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z288,z4,z5,z6])],[(0,[z136,z0,z1,z22,z4,z5,z6]),(0,[z0,z1,z289,z22,z4,z5,z6]),(0,[z96,z0,z1,z2,z4,z30,z6]),(0,[z0,z1,z2,z4,z5,z216,z6]),(0,[z290,z0,z1,z2,z4,z5,z6])],[(0,[z138,z0,z184,z2,z4,z5,z6]),(0,[z25,z0,z103,z1,z4,z5,z6]),(0,[z0,z1,z2,z291,z4,z5,z6]),(0,[z25,z0,z1,z4,z4,z5,z6])],[(0,[z0,z1,z33,z4,z30,z5,z6]),(0,[z25,z0,z1,z4,z5,z6,z206]),(0,[z0,z1,z90,z33,z4,z5,z6]),(0,[z0,z1,z292,z2,z4,z5,z6]),(0,[z0,z1,z293,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z294,z6]),(0,[z32,z0,z1,z21,z4,z5,z6]),(0,[z169,z0,z1,z58,z4,z5,z6]),(0,[z0,z295,z1,z2,z4,z5,z6]),(1,[z25,z0,z1,z4,z5,z6])]],
   [[(0,[z0,z12,z1,z22,z4,z5,z6]),(1,[z0,z1,z222,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z296])],[(0,[z297,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z298,z5,z6]),(0,[z0,z1,z22,z79,z4,z5,z6]),(1,[z0,z1,z299,z4,z5,z6])],[(0,[z0,z1,z2,z4,z300,z5,z6]),(0,[z0,z1,z301,z21,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z182,z6])],[(0,[z0,z1,z1,z2,z4,z5,z6]),(0,[z0,z1,z45,z22,z4,z5,z6]),(1,[z0,z1,z302,z4,z5,z6]),(0,[z0,z1,z2,z4,z303,z5,z6]),(0,[z25,z25,z0,z1,z4,z5,z6]),(0,[z304,z25,z0,z1,z4,z5,z6])],[(0,[z305,z0,z1,z2,z4,z5,z6]),(0,[z0,z66,z1,z21,z4,z5,z6]),(0,[z0,z1,z306,z2,z4,z5,z6]),(0,[z136,z0,z1,z70,z4,z5,z6]),(0,[z0,z1,z2,z4,z39,z5,z6]),(0,[z0,z1,z2,z4,z5,z307,z6])],[(0,[z0,z1,z21,z4,z281,z5,z6]),(0,[z0,z1,z2,z4,z308,z5,z6]),(1,[z0,z1,z242,z4,z5,z6]),(0,[z309,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z310,z4,z5,z6]),(0,[z0,z2,z4,z29,z5,z216,z6]),(0,[z0,z1,z2,z4,z311,z5,z6])],[(0,[z138,z0,z1,z312,z4,z5,z6]),(1,[z57,z1,z2,z84,z5,z6]),(0,[z0,z221,z1,z203,z4,z5,z6]),(0,[z0,z1,z95,z33,z4,z5,z6]),(0,[z0,z74,z1,z2,z4,z5,z46]),(0,[z0,z1,z2,z4,z313,z5,z6])],[(0,[z0,z1,z21,z4,z5,z216,z6]),(0,[z0,z1,z2,z4,z314,z5,z6]),(0,[z0,z1,z33,z4,z19,z5,z6])]],
   [[(0,[z160,z0,z1,z33,z4,z5,z6]),(0,[z0,z1,z2,z69,z58,z5,z6]),(0,[z0,z1,z2,z4,z315,z5,z6]),(0,[z0,z1,z2,z4,z5,z27,z26])],[(0,[z0,z1,z2,z312,z4,z5,z6]),(1,[z0,z1,z255,z4,z5,z6]),(0,[z28,z0,z1,z2,z316,z5,z6]),(0,[z0,z1,z2,z4,z317,z5,z6]),(0,[z0,z1,z2,z4,z318,z5,z6]),(0,[z0,z1,z319,z2,z4,z5,z6]),(1,[z0,z1,z4,z5,z6,z320])],[(1,[z0,z1,z321,z4,z5,z6]),(0,[z0,z1,z21,z4,z5,z81,z6]),(0,[z0,z1,z2,z4,z5,z322,z6]),(0,[z168,z1,z2,z4,z5,z185,z6]),(0,[z0,z1,z2,z4,z323,z5,z6]),(0,[z0,z103,z1,z2,z4,z5,z26]),(1,[z0,z77,z1,z4,z19,z6]),(0,[z32,z0,z1,z2,z118,z5,z6]),(0,[z324,z0,z1,z2,z4,z5,z6]),(0,[z0,z325,z1,z2,z4,z5,z6])],[(0,[z11,z0,z184,z2,z4,z5,z6]),(0,[z96,z0,z1,z2,z4,z59,z6]),(0,[z0,z1,z2,z4,z5,z59,z6]),(0,[z0,z1,z326,z2,z4,z5,z6]),(0,[z0,z1,z2,z327,z4,z5,z6]),(0,[z0,z1,z2,z4,z328,z5,z6]),(0,[z0,z1,z2,z4,z80,z5,z6]),(0,[z0,z1,z2,z4,z5,z329,z6]),(0,[z32,z0,z1,z2,z4,z48,z5]),(0,[z0,z1,z2,z118,z4,z48,z5])],[(0,[z0,z221,z1,z33,z4,z5,z6]),(0,[z330,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z331,z6]),(0,[z0,z1,z332,z2,z4,z5,z6])],[(0,[z0,z1,z62,z22,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z333]),(0,[z25,z0,z155,z1,z4,z5,z6])],[(0,[z138,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z22,z4,z5,z6,z206]),(0,[z96,z0,z1,z33,z4,z5,z6]),(1,[z0,z1,z90,z33,z5,z6]),(0,[z187,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z5,z6,z36])],[(0,[z138,z0,z2,z4,z39,z5,z6]),(0,[z0,z1,z21,z4,z39,z5,z6]),(0,[z57,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z334,z4,z5,z6]),(0,[z0,z335,z1,z2,z4,z5,z6]),(1,[z0,z228,z2,z4,z5,z6]),(0,[z0,z1,z35,z4,z5,z6,z37]),(1,[z0,z1,z4,z5,z6,z271])]],
   [[(0,[z0,z1,z2,z69,z84,z5,z6]),(0,[z25,z114,z0,z1,z4,z5,z6]),(0,[z0,z1,z33,z4,z5,z6,z27]),(0,[z0,z66,z1,z336,z4,z5,z6]),(0,[z0,z1,z120,z2,z4,z6,z206])],[(0,[z337,z0,z1,z21,z4,z5,z6]),(0,[z0,z1,z2,z4,z338,z5,z6]),(0,[z0,z1,z2,z4,z5,z339,z6]),(0,[z0,z1,z2,z4,z5,z340,z6]),(0,[z0,z1,z2,z4,z5,z207,z6])],[(0,[z245,z0,z1,z33,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z341]),(0,[z0,z12,z1,z2,z4,z216,z6]),(0,[z32,z25,z0,z1,z4,z5,z6]),(0,[z0,z1,z2,z4,z342,z5,z6]),(0,[z0,z1,z2,z121,z4,z5,z6])],[(0,[z0,z1,z166,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z343]),(0,[z132,z0,z1,z21,z4,z5,z6]),(0,[z169,z0,z1,z2,z4,z5,z6]),(0,[z136,z1,z2,z4,z5,z6,z27]),(0,[z0,z1,z2,z4,z5,z344,z6]),(0,[z345,z0,z1,z2,z4,z5,z6]),(0,[z25,z0,z1,z45,z4,z5,z6]),(0,[z0,z77,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z346,z4,z5,z6]),(0,[z0,z347,z2,z4,z5,z59,z6]),(0,[z0,z221,z1,z31,z4,z5,z6]),(0,[z0,z348,z1,z2,z4,z5,z6]),(0,[z0,z349,z1,z2,z4,z5,z6])],[(0,[z160,z1,z21,z2,z4,z5,z6]),(0,[z0,z1,z21,z4,z5,z322,z6]),(0,[z0,z350,z1,z2,z4,z5,z6]),(0,[z0,z1,z104,z2,z79,z4,z6])],[(1,[z0,z1,z2,z4,z5,z285]),(0,[z109,z0,z1,z22,z4,z5,z6]),(0,[z0,z1,z21,z4,z5,z59,z6]),(0,[z0,z1,z21,z4,z80,z5,z6]),(0,[z0,z1,z174,z2,z4,z5,z6]),(0,[z108,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z351,z6])],[(0,[z0,z1,z352,z2,z4,z5,z6]),(0,[z32,z0,z1,z2,z4,z5,z81]),(0,[z0,z1,z2,z118,z4,z5,z81]),(0,[z0,z1,z2,z118,z5,z81,z6])]],
   [[(1,[z0,z353,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z354]),(0,[z0,z355,z1,z2,z4,z5,z6]),(0,[z25,z0,z1,z4,z5,z216,z6])],[],[(0,[z0,z1,z2,z4,z91,z5,z6]),(0,[z0,z1,z33,z79,z4,z5,z6]),(0,[z356,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z357,z2,z4,z5,z6]),(0,[z114,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z141,z4,z5,z6])],[(0,[z11,z0,z1,z2,z4,z5,z6]),(0,[z0,z191,z1,z2,z4,z5,z6]),(0,[z0,z1,z21,z4,z5,z207,z6]),(0,[z28,z0,z203,z2,z4,z5,z6]),(0,[z25,z0,z1,z2,z69,z5,z6]),(0,[z358,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z359,z4,z5,z6,z206])],[(0,[z138,z0,z1,z2,z4,z5,z360]),(0,[z11,z0,z2,z4,z39,z5,z6]),(0,[z361,z0,z1,z2,z4,z5,z6]),(0,[z0,z23,z103,z2,z4,z5,z6])],[(0,[z138,z0,z166,z2,z4,z5,z6]),(0,[z11,z184,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z362,z6]),(0,[z0,z1,z2,z4,z5,z6,z363]),(0,[z0,z364,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z365,z4,z5,z6]),(0,[z0,z1,z2,z4,z30,z216,z6]),(0,[z1,z2,z4,z5,z185,z6,z27]),(0,[z0,z1,z366,z2,z4,z5,z6]),(0,[z0,z1,z33,z4,z5,z6,z26])]],
   [[(0,[z0,z1,z2,z4,z5,z360,z6]),(0,[z367,z0,z1,z2,z4,z5,z6]),(0,[z136,z0,z1,z33,z4,z5,z6]),(0,[z25,z0,z1,z4,z39,z5,z6]),(0,[z0,z1,z2,z368,z4,z5,z6]),(1,[z0,z1,z2,z4,z6,z369])],[(1,[z0,z1,z312,z4,z5,z6]),(0,[z184,z1,z166,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z370,z6]),(0,[z96,z0,z1,z260,z4,z5,z6]),(0,[z0,z371,z1,z2,z4,z5,z6]),(0,[z25,z0,z1,z104,z4,z5,z6])],[(0,[z0,z1,z21,z21,z4,z5,z6]),(0,[z0,z23,z1,z21,z4,z5,z6]),(0,[z0,z1,z21,z31,z4,z5,z6]),(0,[z372,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z373,z2,z4,z5,z6]),(1,[z25,z0,z1,z39,z5,z6]),(0,[z374,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z271,z37])],[(1,[z0,z1,z327,z4,z5,z6]),(0,[z0,z1,z2,z336,z4,z5,z6]),(0,[z0,z1,z2,z4,z375,z5,z6]),(0,[z0,z1,z2,z4,z376,z5,z6])],[(0,[z0,z1,z2,z4,z5,z115,z185]),(0,[z0,z12,z1,z33,z4,z5,z6])],[(0,[z0,z1,z22,z4,z48,z5,z6]),(0,[z0,z1,z21,z4,z91,z5,z6]),(0,[z0,z353,z2,z4,z5,z6,z27])],[(0,[z158,z0,z1,z22,z4,z5,z6]),(0,[z0,z1,z13,z22,z4,z5,z6]),(0,[z0,z164,z1,z2,z4,z5,z6]),(0,[z377,z0,z1,z2,z4,z5,z6]),(0,[z0,z74,z77,z1,z4,z5,z6]),(0,[z0,z1,z2,z4,z378,z5,z6]),(0,[z0,z379,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z207,z6,z37])],[(0,[z25,z0,z1,z4,z5,z59,z6]),(1,[z0,z1,z334,z4,z5,z6]),(1,[z0,z219,z1,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z380,z6]),(0,[z25,z97,z0,z1,z4,z5,z6]),(0,[z25,z0,z1,z4,z80,z5,z6]),(0,[z25,z0,z1,z2,z33,z5,z6]),(0,[z0,z1,z45,z33,z4,z5,z6]),(0,[z0,z1,z88,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z22,z4,z5,z216,z6]),(0,[z0,z1,z2,z4,z5,z381,z6]),(0,[z0,z203,z2,z31,z4,z5,z6]),(0,[z0,z1,z299,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z382,z5,z6])],[(0,[z138,z0,z1,z2,z4,z200,z6]),(0,[z0,z1,z2,z4,z5,z383,z6]),(1,[z0,z1,z4,z5,z340,z6]),(0,[z384,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z385,z5,z6]),(0,[z0,z164,z66,z2,z4,z5,z6]),(0,[z386,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z387,z5,z6]),(0,[z0,z1,z388,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z389]),(1,[z0,z1,z121,z4,z5,z6])],[(0,[z123,z0,z1,z22,z4,z5,z6]),(0,[z0,z1,z22,z4,z5,z81,z6]),(0,[z0,z74,z1,z21,z4,z5,z6]),(0,[z0,z1,z390,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z391,z5,z6]),(0,[z0,z1,z392,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z393,z6])],[(0,[z11,z0,z166,z2,z4,z5,z6]),(0,[z0,z1,z21,z4,z5,z370,z6]),(0,[z0,z1,z2,z4,z5,z6,z394]),(0,[z0,z1,z2,z4,z5,z395,z6])],[(0,[z0,z1,z2,z4,z396,z5,z6]),(0,[z25,z0,z1,z4,z5,z207,z6]),(0,[z0,z1,z397,z2,z4,z5,z6])],[(0,[z25,z0,z184,z1,z4,z5,z6]),(0,[z0,z0,z1,z22,z4,z5,z6]),(0,[z398,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z203,z2,z4,z5,z6]),(0,[z25,z0,z77,z1,z4,z5,z6]),(0,[z0,z1,z4,z80,z5,z340,z6])],[(0,[z399,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z400,z5,z6]),(0,[z0,z1,z45,z21,z4,z5,z6]),(0,[z0,z1,z302,z2,z4,z5,z6]),(0,[z401,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z138,z0,z2,z4,z5,z115,z6]),(0,[z0,z184,z1,z22,z4,z5,z6]),(0,[z0,z1,z22,z4,z39,z5,z6]),(0,[z402,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z316,z4,z5,z6]),(0,[z403,z0,z1,z2,z4,z5,z6]),(0,[z404,z0,z1,z2,z4,z5,z6]),(0,[z0,z103,z1,z2,z4,z5,z6]),(0,[z0,z1,z33,z4,z405,z5,z6])],[(0,[z406,z0,z1,z2,z4,z5,z6]),(0,[z65,z0,z1,z33,z4,z5,z6]),(0,[z0,z77,z1,z2,z4,z34,z6]),(1,[z0,z1,z2,z4,z5,z329]),(0,[z0,z1,z2,z4,z48,z207,z6])],[(0,[z96,z1,z2,z4,z30,z5,z6]),(0,[z0,z1,z2,z4,z407,z5,z6]),(0,[z0,z1,z90,z2,z69,z5,z6]),(0,[z0,z1,z13,z4,z5,z34,z6]),(0,[z408,z0,z1,z2,z4,z5,z6])],[(0,[z25,z0,z1,z21,z4,z5,z6]),(0,[z0,z409,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z14,z6])],[(0,[z0,z1,z410,z2,z4,z5,z6]),(0,[z0,z1,z2,z411,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z412]),(0,[z0,z1,z2,z4,z5,z6,z320])],[(0,[z0,z1,z2,z4,z5,z413,z6]),(0,[z0,z1,z2,z321,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z414]),(0,[z0,z2,z4,z5,z344,z6,z27]),(0,[z415,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z416,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z417,z5,z6])],[(0,[z0,z1,z2,z4,z5,z418,z6]),(0,[z0,z1,z42,z21,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z419,z6]),(0,[z25,z0,z1,z4,z91,z5,z6]),(0,[z0,z1,z2,z4,z420,z5,z6])],[(1,[z0,z1,z2,z173,z5,z6]),(0,[z0,z1,z22,z4,z5,z59,z6]),(0,[z0,z1,z22,z4,z80,z5,z6]),(0,[z114,z0,z1,z421,z4,z5,z6]),(1,[z0,z2,z4,z338,z5,z6]),(0,[z0,z1,z33,z4,z5,z6,z37]),(0,[z0,z1,z422,z2,z4,z5,z6]),(0,[z109,z0,z1,z2,z79,z5,z6]),(0,[z0,z1,z2,z79,z4,z80,z6])]],
   [[(0,[z0,z215,z1,z22,z4,z5,z6]),(1,[z25,z0,z1,z91,z5,z6]),(0,[z0,z1,z4,z19,z5,z34,z6])],[(0,[z0,z1,z2,z4,z423,z5,z6]),(0,[z0,z1,z2,z4,z5,z424,z6]),(0,[z168,z0,z1,z327,z4,z5,z6]),(0,[z425,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z426,z6]),(0,[z108,z0,z1,z2,z39,z5,z6]),(0,[z0,z23,z1,z2,z4,z5,z26]),(0,[z0,z1,z427,z2,z4,z5,z6]),(0,[z0,z253,z1,z2,z4,z5,z6])],[(0,[z109,z0,z1,z33,z4,z5,z6]),(0,[z0,z1,z2,z4,z428,z5,z6]),(0,[z0,z429,z1,z2,z4,z5,z6]),(1,[z0,z1,z233,z4,z5,z6]),(0,[z0,z1,z233,z2,z4,z5,z6])],[(1,[z0,z1,z336,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z430,z6])],[(0,[z0,z1,z431,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z185,z26]),(0,[z0,z1,z33,z4,z5,z34,z6]),(0,[z0,z1,z2,z4,z5,z6,z117]),(0,[z109,z0,z1,z104,z2,z4,z6]),(0,[z32,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z118,z4,z5,z6]),(1,[z0,z325,z1,z4,z5,z6])],[(0,[z432,z0,z1,z2,z4,z5,z6]),(0,[z433,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z22,z4,z5,z207,z6]),(0,[z123,z0,z1,z2,z4,z30,z6]),(0,[z0,z1,z2,z4,z5,z6,z434]),(0,[z0,z435,z1,z2,z4,z5,z6]),(0,[z0,z1,z90,z2,z33,z5,z6]),(0,[z109,z0,z1,z2,z4,z207,z6])],[(0,[z11,z0,z2,z4,z5,z115,z6]),(0,[z0,z1,z21,z4,z5,z14,z6]),(0,[z0,z1,z2,z4,z5,z436,z6]),(0,[z25,z168,z0,z1,z4,z5,z6]),(0,[z0,z1,z33,z4,z48,z5,z6]),(0,[z0,z77,z1,z4,z19,z5,z6]),(0,[z437,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z301,z2,z4,z5,z6]),(0,[z0,z1,z33,z4,z5,z54,z6])]],
   [[(0,[z0,z1,z21,z321,z4,z5,z6]),(0,[z0,z1,z2,z58,z4,z5,z6]),(0,[z438,z25,z0,z1,z4,z5,z6]),(0,[z439,z25,z0,z1,z4,z5,z6])],[(0,[z28,z0,z221,z2,z4,z5,z6]),(0,[z0,z66,z1,z2,z4,z5,z6]),(0,[z25,z108,z0,z1,z4,z5,z6]),(0,[z0,z66,z1,z440,z4,z5,z6]),(0,[z0,z12,z164,z2,z4,z5,z6]),(1,[z0,z23,z2,z4,z5,z115]),(0,[z25,z0,z1,z4,z5,z115,z6]),(0,[z0,z1,z441,z2,z4,z5,z6]),(0,[z0,z442,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z443]),(0,[z0,z444,z1,z2,z4,z5,z6])],[(0,[z138,z0,z1,z2,z445,z5,z6]),(0,[z0,z1,z22,z31,z4,z5,z6]),(0,[z0,z446,z1,z2,z4,z5,z6]),(1,[z0,z347,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z447,z6]),(0,[z0,z1,z2,z4,z448,z5,z6]),(1,[z0,z1,z4,z5,z393,z6])],[(1,[z0,z1,z2,z4,z200,z6]),(0,[z449,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z450]),(0,[z0,z1,z33,z4,z5,z81,z6]),(0,[z0,z1,z2,z4,z451,z5,z6])],[(1,[z1,z21,z22,z4,z5,z6]),(0,[z28,z0,z1,z22,z4,z5,z6]),(0,[z168,z0,z1,z21,z4,z5,z6]),(0,[z136,z0,z1,z255,z4,z5,z6]),(1,[z0,z74,z1,z4,z5,z14])],[(0,[z0,z1,z22,z4,z91,z5,z6]),(1,[z0,z100,z1,z4,z5,z6]),(0,[z0,z1,z2,z4,z452,z5,z6]),(0,[z0,z1,z4,z5,z393,z54,z6]),(0,[z0,z1,z2,z453,z4,z5,z6])],[(0,[z138,z1,z166,z2,z4,z5,z6]),(0,[z0,z1,z21,z118,z4,z5,z6]),(0,[z57,z0,z1,z454,z4,z5,z6]),(0,[z114,z0,z1,z455,z4,z5,z6]),(0,[z0,z1,z456,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z457]),(0,[z0,z1,z458,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z459])]],
   [[(1,[z245,z1,z22,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z460,z6])],[(0,[z138,z0,z1,z2,z4,z151,z6]),(0,[z25,z123,z0,z1,z4,z5,z6]),(0,[z0,z1,z104,z2,z4,z5,z6])],[(0,[z0,z461,z1,z21,z4,z5,z6]),(0,[z0,z1,z21,z90,z4,z5,z6]),(0,[z462,z0,z1,z2,z4,z5,z6]),(1,[z0,z164,z2,z4,z29,z6]),(0,[z0,z1,z13,z33,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z369])],[(0,[z0,z1,z463,z2,z4,z5,z6]),(0,[z0,z1,z21,z58,z4,z5,z6]),(0,[z464,z0,z1,z2,z4,z5,z6]),(0,[z465,z0,z1,z2,z4,z5,z6]),(0,[z0,z466,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z163,z6])],[(0,[z0,z1,z2,z467,z4,z5,z6]),(0,[z123,z0,z1,z2,z4,z59,z6]),(0,[z0,z468,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z469,z6]),(0,[z116,z0,z1,z2,z4,z5,z6])],[(0,[z168,z0,z1,z2,z4,z5,z27]),(0,[z0,z1,z2,z4,z5,z470,z6]),(0,[z0,z1,z2,z471,z4,z5,z6]),(0,[z0,z1,z45,z2,z4,z5,z46])],[(0,[z337,z0,z1,z2,z4,z5,z6]),(0,[z0,z472,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z29,z5,z6]),(0,[z0,z1,z473,z2,z4,z5,z6]),(0,[z474,z0,z1,z2,z4,z5,z6]),(0,[z0,z74,z1,z45,z4,z5,z6]),(0,[z0,z1,z475,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z84,z5,z6]),(0,[z123,z0,z1,z33,z4,z5,z6]),(0,[z0,z347,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z476,z4,z5,z6]),(0,[z25,z0,z1,z4,z5,z14,z6]),(0,[z0,z1,z2,z4,z5,z477,z6])]],
   [[(0,[z132,z0,z1,z2,z4,z5,z6]),(0,[z478,z0,z1,z2,z4,z5,z6]),(0,[z212,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z79,z4,z207,z6]),(1,[z0,z364,z2,z4,z5,z6]),(0,[z0,z479,z1,z2,z4,z5,z6])],[(0,[z480,z0,z1,z2,z4,z5,z6]),(0,[z96,z0,z1,z334,z4,z5,z6]),(0,[z0,z481,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z482,z6]),(0,[z25,z0,z74,z1,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z483,z6]),(0,[z0,z1,z2,z484,z4,z5,z6]),(0,[z0,z1,z2,z485,z4,z5,z6]),(0,[z0,z1,z2,z486,z4,z5,z6])],[(0,[z487,z0,z1,z2,z4,z5,z6]),(0,[z160,z0,z1,z21,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z488,z6]),(0,[z0,z1,z2,z489,z4,z5,z6])],[(0,[z0,z184,z1,z33,z4,z5,z6]),(0,[z0,z1,z2,z2,z4,z5,z6]),(0,[z0,z490,z1,z2,z4,z5,z6]),(0,[z491,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z33,z33,z4,z5,z6]),(0,[z492,z0,z1,z2,z4,z5,z6])],[(1,[z138,z166,z2,z4,z5,z6]),(0,[z138,z0,z66,z2,z4,z5,z6]),(0,[z0,z1,z493,z2,z4,z5,z6]),(1,[z0,z1,z455,z4,z5,z6]),(0,[z109,z25,z0,z1,z4,z5,z6]),(0,[z0,z1,z2,z4,z494,z5,z6]),(0,[z0,z1,z2,z4,z495,z5,z6])],[(0,[z0,z1,z2,z4,z5,z496,z6])],[(0,[z123,z0,z1,z21,z4,z5,z6]),(0,[z0,z221,z1,z21,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z497,z6])]],
   [[(0,[z498,z0,z1,z2,z4,z5,z6]),(1,[z114,z1,z2,z58,z5,z6]),(0,[z0,z1,z2,z4,z5,z499,z6]),(0,[z25,z0,z1,z118,z4,z5,z6])],[(0,[z138,z0,z2,z4,z29,z5,z6]),(0,[z11,z0,z1,z145,z4,z5,z6]),(0,[z96,z0,z1,z21,z4,z5,z6]),(1,[z169,z0,z1,z4,z5,z6]),(0,[z0,z500,z1,z2,z4,z5,z6]),(0,[z0,z1,z501,z2,z4,z5,z6]),(0,[z127,z25,z0,z1,z4,z5,z6])],[(0,[z502,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z21,z4,z84,z5,z6]),(0,[z1,z2,z58,z4,z84,z5,z6]),(0,[z0,z1,z2,z4,z503,z5,z6]),(0,[z0,z1,z504,z2,z4,z5,z6]),(0,[z0,z1,z2,z505,z4,z5,z6]),(0,[z506,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z507,z5,z6]),(0,[z0,z1,z104,z2,z4,z48,z6])],[(0,[z160,z245,z1,z2,z4,z5,z6]),(0,[z25,z0,z1,z90,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z46]),(0,[z0,z1,z2,z508,z4,z5,z6])],[(0,[z25,z0,z1,z58,z4,z5,z6]),(0,[z509,z0,z1,z2,z4,z5,z6]),(0,[z510,z0,z1,z2,z4,z5,z6])],[(0,[z245,z0,z1,z21,z4,z5,z6]),(1,[z123,z1,z2,z4,z59,z6]),(0,[z108,z0,z66,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z511,z6]),(0,[z0,z77,z1,z4,z5,z6,z46]),(0,[z0,z512,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z513,z6])],[(1,[z0,z1,z2,z445,z5,z6]),(0,[z25,z0,z1,z166,z4,z5,z6]),(0,[z0,z1,z2,z4,z514,z5,z6])],[(0,[z0,z1,z21,z2,z4,z5,z6]),(0,[z0,z1,z21,z431,z4,z5,z6]),(1,[z0,z66,z2,z69,z5,z6]),(0,[z0,z23,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z515,z1,z2,z4,z5,z6]),(0,[z0,z23,z2,z4,z39,z5,z6]),(0,[z0,z1,z440,z2,z4,z5,z6]),(0,[z0,z1,z516,z2,z4,z5,z6]),(0,[z0,z74,z1,z2,z4,z5,z14])],[(1,[z0,z1,z101,z4,z5,z6]),(0,[z25,z0,z1,z4,z5,z6,z27]),(0,[z0,z1,z2,z4,z237,z5,z6]),(0,[z0,z1,z2,z4,z517,z5,z6]),(0,[z0,z1,z2,z518,z4,z5,z6]),(0,[z32,z0,z1,z2,z4,z5,z206]),(0,[z0,z1,z2,z118,z4,z5,z206]),(0,[z0,z1,z519,z2,z4,z5,z6])],[(0,[z138,z0,z1,z22,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z185,z6]),(0,[z0,z520,z1,z2,z4,z5,z6]),(0,[z0,z12,z2,z4,z5,z216,z6]),(1,[z32,z0,z1,z2,z5,z206]),(0,[z0,z1,z104,z2,z4,z6,z37])],[(0,[z11,z0,z66,z2,z4,z5,z6]),(0,[z25,z11,z0,z1,z4,z5,z6]),(0,[z57,z0,z1,z22,z4,z5,z6]),(0,[z0,z1,z49,z2,z4,z5,z6]),(0,[z0,z1,z2,z58,z39,z5,z6]),(0,[z28,z0,z1,z203,z4,z5,z6]),(0,[z0,z1,z2,z521,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z522]),(0,[z32,z0,z364,z2,z4,z5,z6]),(1,[z0,z1,z4,z5,z6,z523]),(0,[z0,z524,z1,z2,z4,z5,z6])],[(0,[z0,z1,z56,z2,z4,z5,z6]),(0,[z0,z1,z2,z525,z4,z5,z6]),(0,[z136,z0,z1,z2,z4,z5,z185]),(0,[z0,z66,z1,z2,z39,z5,z6]),(0,[z0,z1,z45,z2,z4,z5,z14]),(0,[z0,z1,z4,z5,z6,z320,z206])],[(0,[z526,z0,z1,z2,z4,z5,z6]),(0,[z0,z221,z2,z31,z4,z5,z6]),(0,[z109,z0,z228,z2,z4,z5,z6]),(0,[z0,z1,z527,z2,z4,z5,z6])],[(0,[z528,z0,z1,z2,z4,z5,z6]),(0,[z160,z25,z0,z1,z4,z5,z6]),(0,[z0,z529,z1,z21,z4,z5,z6]),(0,[z0,z1,z21,z4,z5,z6,z46]),(0,[z0,z1,z2,z4,z530,z5,z6]),(0,[z531,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z532]),(0,[z32,z0,z1,z2,z80,z5,z6])],[(0,[z0,z1,z166,z22,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z533,z6]),(0,[z11,z0,z2,z4,z29,z5,z6]),(0,[z0,z77,z1,z22,z4,z5,z6]),(0,[z0,z534,z1,z2,z4,z5,z6]),(1,[z0,z12,z2,z4,z216,z6]),(0,[z0,z1,z2,z4,z5,z6,z535]),(0,[z0,z536,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z537,z6]),(0,[z109,z0,z1,z2,z4,z80,z6])]],
   [[(0,[z0,z538,z1,z2,z4,z5,z6]),(0,[z245,z1,z2,z22,z4,z5,z6]),(0,[z0,z1,z22,z118,z4,z5,z6]),(0,[z0,z1,z2,z4,z171,z5,z6]),(0,[z0,z1,z539,z2,z4,z5,z6]),(0,[z0,z1,z2,z540,z4,z5,z6]),(0,[z0,z1,z2,z4,z541,z5,z6]),(0,[z0,z1,z2,z4,z5,z115,z6]),(0,[z0,z1,z2,z4,z5,z542,z6]),(0,[z0,z74,z1,z2,z4,z5,z6])],[(0,[z28,z0,z1,z33,z4,z5,z6]),(0,[z0,z1,z69,z33,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z543,z6]),(0,[z0,z1,z33,z4,z4,z5,z6])],[(0,[z108,z0,z1,z22,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z544]),(0,[z545,z0,z1,z2,z4,z5,z6]),(0,[z25,z0,z1,z4,z29,z5,z6]),(0,[z0,z1,z33,z4,z5,z6,z206]),(0,[z0,z1,z2,z4,z261,z5,z6]),(0,[z0,z546,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z547,z4,z5,z6])],[(0,[z136,z0,z1,z21,z4,z5,z6]),(0,[z25,z0,z1,z4,z84,z5,z6]),(0,[z0,z548,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z6,z369,z206])],[(1,[z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z22,z58,z4,z5,z6]),(0,[z0,z1,z549,z21,z4,z5,z6]),(0,[z0,z1,z550,z2,z4,z5,z6]),(1,[z0,z1,z440,z4,z5,z6]),(0,[z551,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z21,z4,z5,z185,z6]),(0,[z0,z552,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z553,z6]),(0,[z0,z1,z2,z4,z554,z5,z6]),(0,[z267,z0,z1,z33,z4,z5,z6])],[],[(0,[z114,z0,z1,z22,z4,z5,z6]),(0,[z0,z12,z1,z21,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z555,z6]),(0,[z0,z556,z1,z2,z4,z5,z6]),(0,[z0,z164,z1,z2,z4,z29,z6])]],
   [[(0,[z11,z0,z1,z22,z4,z5,z6]),(0,[z0,z1,z2,z421,z4,z5,z6]),(0,[z123,z0,z1,z242,z4,z5,z6]),(0,[z0,z1,z557,z2,z4,z5,z6]),(0,[z25,z0,z1,z2,z4,z5,z6]),(0,[z304,z0,z1,z2,z4,z5,z6]),(0,[z558,z0,z1,z2,z4,z5,z6])],[(0,[z28,z0,z1,z2,z237,z5,z6]),(0,[z0,z164,z2,z4,z29,z5,z6]),(0,[z25,z0,z1,z4,z494,z5,z6])],[(0,[z559,z0,z1,z2,z4,z5,z6]),(0,[z0,z560,z1,z2,z4,z5,z6]),(0,[z561,z0,z1,z2,z4,z5,z6]),(1,[z0,z287,z1,z4,z5,z6]),(0,[z0,z325,z1,z4,z5,z81,z6]),(0,[z0,z1,z562,z2,z4,z5,z6])],[(0,[z0,z1,z2,z563,z4,z5,z6]),(0,[z0,z1,z21,z4,z5,z115,z6]),(0,[z564,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z565,z5,z6]),(0,[z566,z0,z1,z2,z4,z5,z6]),(0,[z136,z0,z1,z2,z4,z5,z27]),(0,[z0,z1,z2,z4,z5,z567,z6]),(0,[z0,z232,z1,z2,z4,z5,z6])],[(0,[z1,z21,z2,z22,z4,z5,z6]),(0,[z32,z0,z1,z104,z2,z4,z5])],[(0,[z0,z1,z2,z4,z5,z6,z568]),(0,[z0,z1,z2,z4,z5,z6,z569]),(0,[z0,z1,z2,z4,z5,z570,z6]),(0,[z571,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z13,z45,z4,z5,z6]),(0,[z0,z1,z572,z2,z4,z5,z6]),(0,[z0,z1,z104,z2,z4,z5,z207])],[(0,[z0,z1,z2,z4,z573,z5,z6]),(0,[z0,z1,z2,z4,z30,z5,z6]),(0,[z0,z1,z574,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z575,z6]),(0,[z25,z0,z287,z1,z4,z5,z6]),(0,[z576,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z577,z5,z6]),(0,[z25,z0,z1,z4,z5,z6,z46])]],
   [[(0,[z0,z1,z2,z578,z4,z5,z6]),(0,[z0,z1,z2,z4,z579,z5,z6]),(0,[z0,z1,z2,z4,z197,z5,z6]),(0,[z251,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z580,z6]),(0,[z581,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z582])],[(0,[z0,z583,z1,z2,z4,z5,z6]),(0,[z584,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z33,z4,z5,z256,z6])],[(0,[z0,z164,z1,z22,z4,z5,z6]),(0,[z585,z0,z1,z2,z4,z5,z6]),(0,[z586,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z95,z58,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z587,z6]),(0,[z0,z1,z2,z588,z4,z5,z6])],[(1,[z0,z1,z2,z4,z5,z360]),(0,[z0,z1,z589,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z590])],[(0,[z0,z1,z2,z4,z591,z5,z6]),(1,[z0,z2,z4,z5,z344,z6]),(0,[z0,z1,z31,z33,z4,z5,z6])],[(0,[z592,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z593,z6]),(0,[z0,z2,z4,z39,z5,z216,z6]),(0,[z0,z1,z594,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z595,z5,z6]),(1,[z0,z1,z4,z405,z5,z6]),(0,[z596,z0,z1,z2,z4,z5,z6])],[(0,[z25,z0,z1,z4,z5,z185,z6]),(0,[z0,z1,z2,z4,z597,z5,z6]),(0,[z0,z1,z2,z80,z5,z54,z6]),(0,[z0,z1,z2,z4,z598,z5,z6])],[(0,[z0,z1,z2,z4,z246,z5,z6]),(0,[z0,z599,z1,z2,z4,z5,z6]),(1,[z0,z221,z31,z4,z5,z6]),(0,[z25,z0,z1,z4,z5,z6,z522]),(0,[z270,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z19,z5,z6])]],
   [[(0,[z168,z136,z1,z2,z4,z5,z6]),(0,[z0,z600,z1,z2,z4,z5,z6]),(0,[z32,z0,z1,z2,z5,z6,z206])],[(0,[z114,z1,z2,z58,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z601,z6]),(0,[z168,z0,z1,z2,z4,z5,z185]),(0,[z0,z103,z2,z4,z5,z6,z26]),(0,[z0,z1,z2,z4,z5,z6,z602])],[(0,[z0,z1,z22,z4,z5,z6,z343]),(0,[z0,z1,z203,z22,z4,z5,z6]),(0,[z168,z0,z1,z2,z4,z5,z6]),(0,[z0,z603,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z604,z6]),(1,[z0,z1,z35,z4,z5,z6])],[(0,[z0,z605,z1,z2,z4,z5,z6]),(0,[z0,z100,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z36])],[(0,[z0,z1,z2,z4,z606,z5,z6]),(0,[z0,z103,z1,z22,z4,z5,z6]),(0,[z57,z1,z2,z4,z84,z5,z6]),(0,[z0,z1,z455,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z607,z5,z6]),(1,[z0,z1,z2,z316,z5,z6]),(0,[z28,z25,z0,z1,z4,z5,z6]),(0,[z0,z1,z33,z4,z5,z216,z6])],[(0,[z109,z0,z1,z21,z4,z5,z6]),(0,[z0,z1,z2,z4,z608,z5,z6])],[(0,[z138,z0,z1,z33,z4,z5,z6]),(0,[z25,z0,z66,z1,z4,z5,z6]),(0,[z0,z1,z90,z2,z4,z5,z6]),(0,[z0,z609,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z79,z80,z6])],[(0,[z0,z461,z1,z2,z4,z5,z6]),(0,[z57,z0,z1,z33,z4,z5,z6]),(0,[z0,z1,z2,z4,z610,z5,z6]),(0,[z0,z1,z2,z4,z5,z611,z6]),(0,[z0,z1,z2,z4,z612,z5,z6]),(0,[z0,z613,z1,z2,z4,z5,z6])]],
   [[(1,[z0,z1,z421,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z27]),(0,[z614,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z615,z6]),(0,[z0,z1,z2,z4,z5,z616,z6]),(0,[z0,z1,z2,z617,z4,z5,z6]),(0,[z618,z0,z1,z2,z4,z5,z6])],[(0,[z0,z188,z1,z2,z4,z5,z6]),(0,[z114,z0,z1,z2,z84,z5,z6]),(1,[z187,z0,z1,z2,z5,z6])],[(0,[z0,z1,z21,z4,z19,z5,z6]),(0,[z0,z1,z2,z4,z5,z619,z6]),(0,[z0,z1,z620,z2,z4,z5,z6]),(0,[z0,z1,z621,z2,z4,z5,z6]),(0,[z0,z74,z1,z4,z5,z14,z6]),(0,[z109,z0,z258,z2,z4,z5,z6])],[(0,[z0,z1,z166,z33,z4,z5,z6]),(0,[z0,z1,z2,z622,z4,z5,z6]),(0,[z0,z623,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z624]),(0,[z0,z77,z1,z33,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z625,z6]),(0,[z0,z1,z299,z4,z5,z54,z6])],[(0,[z0,z1,z2,z454,z4,z5,z6]),(0,[z0,z1,z2,z4,z626,z5,z6]),(0,[z0,z1,z33,z4,z39,z5,z6]),(0,[z0,z164,z1,z2,z4,z216,z6]),(0,[z627,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z628]),(1,[z28,z0,z203,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z629]),(0,[z282,z25,z0,z1,z4,z5,z6]),(0,[z0,z1,z2,z4,z630,z5,z6])],[(0,[z0,z1,z22,z4,z5,z185,z6]),(0,[z0,z1,z631,z2,z4,z5,z6]),(0,[z108,z0,z1,z33,z4,z5,z6]),(0,[z0,z1,z359,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z523])],[(0,[z0,z1,z2,z4,z5,z632,z6]),(0,[z25,z0,z221,z1,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z633]),(0,[z0,z634,z1,z2,z4,z5,z6])]],
   [[(0,[z214,z0,z1,z2,z4,z5,z6]),(0,[z160,z0,z1,z2,z4,z5,z6]),(0,[z32,z0,z1,z22,z4,z5,z6]),(0,[z635,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z636,z6]),(1,[z0,z1,z226,z4,z5,z6]),(0,[z0,z637,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z638])],[(1,[z108,z0,z2,z39,z5,z6]),(0,[z0,z1,z33,z4,z318,z5,z6]),(0,[z0,z1,z2,z4,z5,z639,z6])],[(0,[z640,z0,z1,z2,z4,z5,z6]),(0,[z25,z0,z1,z4,z30,z5,z6]),(0,[z0,z1,z641,z2,z4,z5,z6]),(0,[z0,z66,z2,z4,z5,z6,z26]),(0,[z0,z1,z2,z79,z4,z5,z6])],[(0,[z642,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z21,z4,z5,z6,z27]),(0,[z114,z0,z1,z33,z4,z5,z6]),(0,[z0,z1,z33,z4,z5,z59,z6]),(0,[z0,z1,z2,z4,z5,z643,z6]),(0,[z0,z644,z1,z2,z4,z5,z6]),(0,[z25,z0,z1,z2,z39,z5,z6]),(0,[z0,z1,z33,z4,z80,z5,z6]),(0,[z645,z0,z1,z2,z4,z5,z6]),(0,[z109,z32,z0,z1,z2,z5,z6])],[(0,[z138,z0,z1,z213,z4,z5,z6]),(0,[z11,z0,z1,z33,z4,z5,z6]),(0,[z0,z1,z22,z4,z5,z115,z6]),(0,[z0,z1,z2,z95,z4,z5,z6]),(0,[z0,z221,z1,z2,z4,z5,z6]),(0,[z646,z0,z1,z2,z4,z5,z6])],[(0,[z0,z66,z1,z22,z4,z5,z6]),(0,[z0,z1,z13,z21,z4,z5,z6]),(0,[z57,z114,z1,z2,z4,z5,z6]),(1,[z0,z1,z359,z4,z5,z6])],[(0,[z0,z1,z2,z445,z4,z5,z6]),(0,[z647,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z107,z6]),(0,[z0,z1,z2,z4,z648,z5,z6]),(0,[z0,z1,z21,z4,z5,z6,z624]),(0,[z96,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z5,z6]),(0,[z649,z0,z1,z2,z4,z5,z6]),(0,[z0,z219,z1,z4,z39,z5,z6]),(0,[z0,z1,z650,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z651,z6])],[(0,[z652,z0,z1,z2,z4,z5,z6]),(0,[z0,z446,z1,z22,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z26]),(0,[z653,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z5,z81,z6,z206])]],
   [[(0,[z25,z245,z0,z1,z4,z5,z6]),(0,[z0,z1,z654,z2,z4,z5,z6]),(0,[z109,z0,z1,z2,z5,z54,z6]),(0,[z0,z1,z2,z4,z5,z6,z655])],[(0,[z0,z2,z4,z338,z5,z59,z6]),(0,[z0,z1,z2,z4,z5,z656,z6]),(0,[z0,z103,z1,z2,z4,z5,z115]),(0,[z0,z1,z33,z4,z5,z207,z6]),(0,[z0,z657,z1,z2,z4,z5,z6]),(0,[z0,z1,z4,z5,z81,z6,z523])],[(0,[z245,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z658,z6]),(0,[z0,z1,z2,z4,z659,z5,z6]),(0,[z0,z660,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z661,z6])],[(0,[z0,z1,z2,z4,z5,z6,z662]),(0,[z0,z1,z663,z2,z4,z5,z6]),(0,[z0,z1,z2,z24,z4,z5,z6]),(0,[z0,z664,z1,z2,z4,z5,z6]),(0,[z25,z0,z1,z4,z19,z5,z6]),(0,[z0,z665,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z666,z5,z6])],[(0,[z0,z1,z21,z4,z29,z5,z6]),(0,[z0,z1,z2,z4,z667,z5,z6]),(0,[z668,z0,z1,z2,z4,z5,z6]),(0,[z669,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z104,z22,z4,z5,z6]),(0,[z0,z0,z1,z21,z4,z5,z6]),(0,[z0,z66,z2,z69,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z670]),(0,[z0,z1,z2,z4,z671,z5,z6]),(0,[z109,z0,z1,z2,z5,z81,z6])],[(0,[z672,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z673,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z674]),(0,[z0,z1,z675,z2,z4,z5,z6]),(0,[z0,z164,z1,z33,z4,z5,z6])],[(0,[z0,z184,z1,z21,z4,z5,z6]),(0,[z0,z1,z22,z563,z4,z5,z6]),(0,[z0,z1,z2,z4,z676,z5,z6]),(0,[z0,z1,z126,z2,z4,z5,z6])]],
   [[(0,[z0,z353,z1,z2,z4,z5,z6]),(0,[z0,z677,z1,z2,z4,z5,z6]),(0,[z678,z0,z1,z2,z4,z5,z6])],[(0,[z138,z25,z0,z1,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z679,z6])],[(0,[z0,z1,z22,z4,z5,z14,z6]),(0,[z0,z1,z21,z4,z5,z6,z26]),(0,[z57,z25,z0,z1,z4,z5,z6]),(0,[z680,z0,z1,z2,z4,z5,z6]),(0,[z681,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z69,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z682]),(0,[z0,z1,z33,z4,z91,z5,z6]),(0,[z0,z1,z2,z4,z5,z329,z54]),(1,[z0,z253,z1,z4,z5,z6])],[(0,[z0,z529,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z683,z6]),(0,[z0,z1,z2,z4,z684,z5,z6])],[(0,[z132,z0,z1,z22,z4,z5,z6]),(1,[z0,z1,z454,z4,z5,z6]),(0,[z0,z1,z2,z4,z685,z5,z6]),(0,[z25,z0,z1,z4,z5,z616,z6]),(1,[z109,z0,z1,z2,z54,z6])],[(0,[z686,z0,z1,z2,z4,z5,z6])],[(0,[z57,z0,z1,z302,z4,z5,z6]),(0,[z0,z1,z203,z33,z4,z5,z6]),(0,[z0,z23,z66,z2,z4,z5,z6]),(0,[z169,z25,z0,z1,z4,z5,z6]),(0,[z345,z25,z0,z1,z4,z5,z6]),(0,[z0,z1,z2,z687,z4,z5,z6]),(0,[z0,z1,z688,z2,z4,z5,z6]),(0,[z0,z1,z104,z2,z118,z4,z5])],[(1,[z0,z1,z2,z4,z151,z6]),(0,[z0,z1,z2,z4,z689,z5,z6]),(0,[z0,z1,z2,z4,z690,z5,z6]),(0,[z0,z1,z2,z4,z691,z5,z6])]],
   [[(0,[z0,z1,z2,z22,z4,z5,z6]),(0,[z0,z1,z289,z2,z4,z5,z6]),(0,[z136,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z692,z6]),(0,[z0,z103,z1,z33,z4,z5,z6]),(0,[z0,z1,z2,z4,z405,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z693]),(0,[z0,z1,z2,z4,z48,z5,z37])],[(0,[z0,z1,z549,z2,z4,z5,z6]),(1,[z0,z1,z145,z4,z5,z6]),(0,[z0,z1,z2,z694,z4,z5,z6]),(0,[z0,z1,z90,z2,z39,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z695]),(0,[z25,z0,z1,z2,z91,z5,z6]),(0,[z0,z1,z2,z4,z5,z696,z6]),(0,[z0,z258,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z697,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z285]),(0,[z0,z1,z2,z4,z5,z6,z698]),(0,[z0,z1,z21,z4,z676,z5,z6]),(0,[z0,z699,z1,z2,z4,z5,z6])],[(0,[z0,z1,z22,z4,z19,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z700]),(1,[z25,z0,z1,z69,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z701]),(0,[z0,z1,z156,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z173,z5,z6]),(1,[z0,z1,z95,z4,z5,z6]),(0,[z0,z12,z1,z2,z4,z5,z6])],[(0,[z702,z0,z1,z2,z4,z5,z6]),(0,[z438,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z21,z69,z4,z5,z6]),(0,[z703,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z704,z6]),(0,[z439,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z33,z4,z5,z115,z6]),(1,[z0,z1,z45,z4,z5,z46]),(1,[z0,z1,z88,z2,z4,z5])],[(0,[z25,z0,z1,z79,z4,z5,z6]),(0,[z0,z1,z687,z33,z4,z5,z6])],[(1,[z0,z1,z213,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z179,z6]),(0,[z0,z1,z2,z4,z5,z705,z6]),(0,[z0,z1,z45,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z37]),(0,[z0,z1,z2,z4,z706,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z289,z4,z34,z6]),(0,[z0,z1,z4,z5,z6,z707]),(0,[z649,z0,z1,z33,z5,z6]),(0,[z25,z0,z164,z4,z29,z6]),(0,[z187,z0,z1,z2,z5,z6])],[(0,[z0,z1,z104,z2,z453,z4])],[(0,[z0,z1,z22,z5,z708,z6]),(0,[z0,z709,z1,z4,z5,z6]),(0,[z0,z1,z710,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z711])],[(0,[z0,z1,z2,z4,z712,z6]),(0,[z0,z1,z22,z4,z5,z360]),(0,[z0,z22,z4,z5,z713,z6]),(0,[z0,z2,z4,z714,z5,z6]),(0,[z0,z347,z2,z4,z29,z6])],[(0,[z0,z1,z715,z4,z5,z6]),(0,[z0,z716,z2,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z717]),(0,[z114,z1,z33,z58,z5,z6]),(0,[z25,z0,z718,z4,z5,z6]),(0,[z0,z1,z4,z5,z14,z443])],[(0,[z0,z1,z33,z4,z5,z285]),(0,[z0,z1,z2,z719,z5,z6]),(0,[z0,z1,z21,z5,z6,z36]),(0,[z0,z1,z4,z5,z6,z720]),(0,[z0,z1,z90,z24,z5,z6]),(0,[z0,z2,z4,z5,z115,z721])],[(0,[z0,z722,z2,z4,z5,z6]),(0,[z169,z114,z1,z58,z5,z6]),(0,[z136,z1,z255,z4,z5,z27]),(0,[z0,z1,z440,z39,z5,z6]),(0,[z0,z1,z2,z118,z5,z81])],[(0,[z138,z166,z2,z4,z151,z6]),(0,[z0,z1,z2,z4,z723,z5]),(0,[z0,z1,z226,z4,z5,z6])]],
   [[(0,[z0,z140,z2,z4,z5,z6]),(0,[z0,z103,z2,z4,z5,z285]),(0,[z0,z1,z4,z724,z5,z6]),(0,[z25,z0,z1,z5,z6,z43]),(0,[z0,z1,z725,z4,z5,z6]),(0,[z108,z0,z2,z39,z5,z6])],[(0,[z158,z0,z1,z95,z5,z6]),(0,[z0,z726,z2,z4,z5,z6]),(0,[z727,z0,z1,z4,z5,z6]),(0,[z0,z1,z728,z4,z5,z6])],[(0,[z0,z1,z729,z39,z5,z6]),(0,[z0,z1,z730,z4,z5,z6])],[(0,[z404,z1,z22,z4,z5,z6]),(0,[z0,z156,z21,z4,z5,z6]),(0,[z0,z1,z2,z731,z5,z6])],[(0,[z0,z23,z22,z4,z5,z115]),(0,[z0,z287,z1,z39,z5,z6]),(0,[z251,z1,z95,z4,z5,z6]),(0,[z0,z1,z4,z19,z732,z6]),(0,[z0,z1,z104,z2,z4,z37])],[(0,[z0,z1,z2,z733,z5,z6]),(0,[z0,z1,z2,z4,z734,z6]),(0,[z0,z1,z21,z4,z5,z285]),(0,[z0,z735,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z736]),(0,[z25,z0,z1,z72,z5,z6])],[(0,[z0,z1,z737,z4,z5,z6]),(0,[z0,z1,z22,z79,z80,z6]),(0,[z0,z1,z738,z4,z5,z6]),(0,[z0,z2,z69,z739,z5,z6])],[(0,[z138,z166,z213,z4,z5,z6]),(0,[z0,z1,z22,z4,z200,z6]),(0,[z0,z353,z21,z4,z5,z6]),(0,[z25,z0,z1,z7,z5,z6]),(0,[z0,z1,z4,z5,z740,z6])]],
   [[(0,[z0,z1,z2,z445,z151,z6]),(0,[z0,z741,z1,z4,z5,z6]),(0,[z0,z742,z21,z4,z5,z6]),(0,[z168,z1,z2,z4,z5,z185]),(0,[z743,z1,z2,z4,z5,z6]),(0,[z0,z1,z4,z744,z5,z6]),(0,[z0,z1,z120,z2,z4,z6])],[(0,[z0,z745,z1,z4,z5,z6]),(0,[z0,z1,z45,z4,z5,z624]),(0,[z57,z1,z222,z84,z5,z6])],[(0,[z0,z1,z2,z4,z746,z6]),(0,[z0,z1,z747,z4,z5,z6]),(0,[z0,z1,z748,z4,z5,z6]),(0,[z0,z1,z2,z4,z48,z749])],[(0,[z0,z1,z750,z4,z5,z6]),(0,[z0,z1,z4,z751,z5,z6])],[(0,[z57,z1,z302,z84,z5,z6]),(0,[z0,z1,z4,z5,z752,z46])],[(0,[z0,z2,z4,z197,z5,z6]),(0,[z11,z2,z4,z204,z5,z6]),(0,[z0,z164,z22,z4,z29,z6]),(0,[z0,z753,z22,z4,z5,z6]),(0,[z57,z287,z1,z4,z5,z6]),(0,[z136,z353,z2,z4,z5,z27]),(0,[z25,z754,z1,z4,z5,z6]),(0,[z0,z1,z4,z5,z14,z752]),(0,[z187,z0,z1,z35,z5,z6])],[(0,[z0,z1,z22,z755,z5,z6]),(0,[z0,z1,z756,z4,z5,z6]),(0,[z0,z1,z4,z757,z5,z6]),(0,[z0,z1,z758,z4,z5,z6]),(0,[z0,z1,z4,z5,z759,z6])],[(0,[z25,z0,z1,z578,z5,z6]),(0,[z0,z1,z21,z4,z6,z369]),(0,[z0,z1,z760,z4,z5,z6]),(0,[z1,z2,z4,z30,z761,z6]),(0,[z25,z0,z156,z4,z5,z6]),(0,[z116,z0,z1,z4,z163,z6]),(0,[z0,z74,z1,z4,z5,z752]),(0,[z187,z0,z762,z2,z5,z6])]],
   [[(0,[z0,z1,z33,z4,z5,z6]),(0,[z0,z1,z213,z445,z5,z6]),(0,[z25,z0,z1,z5,z6,z36]),(0,[z0,z1,z763,z4,z5,z6])],[(0,[z1,z22,z4,z5,z380,z6]),(0,[z0,z2,z4,z764,z5,z6]),(0,[z0,z765,z21,z4,z5,z6]),(0,[z109,z0,z228,z2,z54,z6]),(0,[z0,z766,z1,z4,z5,z6])],[(0,[z0,z155,z2,z69,z5,z6])],[(0,[z0,z1,z767,z4,z5,z6]),(0,[z0,z768,z1,z2,z4,z6]),(0,[z0,z364,z22,z4,z5,z6]),(0,[z0,z1,z2,z5,z769,z6]),(0,[z0,z1,z770,z4,z5,z6])],[(0,[z28,z0,z203,z316,z5,z6]),(0,[z0,z1,z2,z4,z5,z771]),(0,[z0,z1,z772,z4,z5,z6])],[(0,[z11,z2,z4,z229,z5,z6]),(0,[z0,z773,z1,z4,z5,z6]),(0,[z1,z2,z58,z774,z5,z6]),(0,[z404,z1,z2,z58,z5,z6]),(1,[z0,z775,z4,z5,z6])],[(0,[z0,z1,z776,z445,z5,z6]),(0,[z0,z1,z777,z4,z5,z6]),(0,[z0,z778,z2,z4,z5,z6]),(0,[z510,z0,z1,z33,z5,z6]),(0,[z32,z0,z1,z33,z5,z206]),(0,[z0,z1,z4,z5,z256,z46]),(0,[z0,z779,z2,z4,z5,z6])],[(0,[z0,z22,z4,z5,z344,z6]),(0,[z0,z1,z22,z4,z780,z5]),(0,[z32,z0,z1,z22,z5,z206]),(0,[z270,z0,z1,z4,z5,z117]),(0,[z0,z1,z781,z4,z5,z6])]],
   [[(0,[z25,z0,z1,z4,z5,z285]),(0,[z138,z166,z22,z4,z5,z6]),(0,[z0,z1,z782,z4,z5,z6]),(0,[z251,z1,z22,z4,z5,z6]),(0,[z783,z0,z1,z2,z5,z6]),(0,[z0,z1,z33,z694,z5,z6]),(0,[z0,z21,z4,z197,z5,z6]),(0,[z57,z1,z4,z405,z5,z6]),(0,[z0,z1,z2,z237,z5,z6]),(0,[z0,z1,z33,z4,z5,z329]),(0,[z0,z1,z2,z4,z48,z207])],[(0,[z0,z1,z2,z784,z5,z6]),(0,[z25,z0,z4,z338,z5,z6]),(0,[z0,z2,z4,z5,z721,z26]),(0,[z0,z1,z104,z2,z4,z602]),(0,[z0,z1,z785,z4,z5,z6])],[(0,[z0,z66,z2,z4,z151,z6]),(0,[z0,z1,z786,z4,z5,z6]),(0,[z25,z0,z1,z69,z5,z6]),(0,[z0,z1,z120,z359,z4,z6]),(0,[z0,z1,z120,z2,z81,z6])],[(0,[z0,z1,z787,z4,z5,z6]),(0,[z0,z1,z22,z5,z6,z788]),(0,[z653,z1,z22,z4,z5,z6]),(0,[z25,z0,z23,z4,z5,z115]),(0,[z0,z789,z1,z4,z5,z6])],[(0,[z0,z1,z790,z4,z5,z6]),(0,[z0,z1,z33,z5,z244,z6]),(0,[z0,z1,z45,z4,z5,z46]),(0,[z0,z1,z88,z2,z4,z5])],[(0,[z11,z184,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z791,z6]),(0,[z0,z1,z792,z4,z5,z6]),(0,[z0,z2,z4,z29,z149,z6]),(0,[z158,z0,z1,z5,z81,z6]),(0,[z169,z0,z4,z197,z5,z6]),(0,[z136,z1,z2,z4,z5,z793]),(0,[z0,z221,z775,z4,z5,z6]),(0,[z25,z0,z258,z4,z5,z6]),(0,[z187,z25,z0,z1,z5,z6]),(0,[z0,z1,z475,z4,z34,z6])],[(0,[z0,z1,z213,z4,z5,z6]),(0,[z0,z2,z4,z29,z151,z6]),(0,[z0,z1,z794,z4,z5,z6]),(0,[z57,z1,z2,z774,z5,z6]),(0,[z0,z353,z2,z4,z5,z26])],[(0,[z0,z1,z2,z4,z5,z795]),(0,[z0,z1,z33,z4,z5,z360]),(0,[z0,z796,z1,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z793]),(0,[z797,z0,z1,z4,z5,z6]),(0,[z0,z12,z2,z4,z798,z6]),(0,[z0,z164,z2,z4,z798,z6])]],
   [[(0,[z123,z1,z22,z4,z59,z6]),(0,[z0,z2,z4,z5,z799,z6]),(0,[z0,z1,z2,z80,z6,z16])],[(0,[z0,z1,z22,z445,z5,z6]),(0,[z0,z800,z1,z2,z4,z5]),(0,[z754,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z5,z801])],[(0,[z109,z158,z0,z1,z5,z6]),(0,[z0,z1,z321,z58,z5,z6]),(0,[z25,z136,z1,z4,z5,z27]),(0,[z1,z2,z4,z5,z6,z802]),(0,[z803,z1,z2,z4,z5,z6])],[(0,[z0,z1,z260,z4,z5,z6]),(0,[z0,z1,z804,z4,z5,z6]),(0,[z0,z805,z2,z4,z5,z6]),(0,[z0,z258,z21,z4,z5,z6]),(0,[z183,z1,z21,z4,z5,z6]),(0,[z0,z140,z2,z39,z5,z6]),(0,[z0,z1,z806,z4,z5,z6]),(0,[z0,z1,z807,z4,z5,z6]),(0,[z25,z0,z1,z20,z5,z6]),(0,[z0,z1,z808,z4,z5,z6]),(0,[z0,z1,z2,z118,z5,z801])],[(0,[z0,z1,z776,z4,z5,z6]),(0,[z0,z1,z2,z809,z5,z6]),(0,[z136,z1,z21,z4,z5,z27]),(0,[z0,z1,z45,z4,z5,z522])],[(0,[z0,z1,z810,z4,z5,z6]),(0,[z25,z0,z1,z33,z5,z6]),(0,[z25,z0,z1,z120,z4,z6]),(0,[z0,z2,z4,z811,z5,z6]),(0,[z0,z1,z812,z4,z5,z6])],[(0,[z0,z1,z21,z173,z5,z6]),(0,[z0,z1,z813,z22,z4,z6]),(0,[z0,z1,z4,z5,z6,z814]),(0,[z815,z0,z1,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z816]),(0,[z0,z1,z22,z4,z151,z6]),(0,[z0,z1,z817,z4,z5,z6]),(0,[z350,z1,z22,z4,z5,z6]),(0,[z0,z1,z818,z4,z5,z6]),(0,[z25,z0,z1,z659,z5,z6]),(0,[z0,z1,z2,z5,z6,z819]),(0,[z0,z1,z88,z2,z80,z5]),(0,[z0,z1,z5,z6,z271,z36])]],
   [[(0,[z0,z820,z1,z4,z5,z6]),(0,[z0,z23,z33,z4,z5,z115]),(0,[z0,z1,z821,z4,z5,z6])],[(0,[z0,z529,z1,z4,z676,z6]),(0,[z0,z2,z739,z39,z5,z6]),(0,[z32,z0,z1,z2,z128,z5])],[(0,[z0,z12,z22,z4,z216,z6]),(0,[z0,z718,z2,z4,z5,z6]),(0,[z0,z822,z2,z4,z5,z6]),(0,[z0,z1,z2,z823,z5,z6]),(0,[z0,z2,z4,z824,z5,z6]),(0,[z0,z1,z825,z4,z5,z6]),(0,[z0,z1,z33,z79,z80,z6])],[(0,[z25,z0,z1,z4,z5,z6]),(0,[z0,z1,z33,z4,z200,z6]),(0,[z0,z1,z826,z4,z5,z6]),(0,[z0,z1,z827,z4,z5,z6])],[(0,[z0,z1,z222,z4,z5,z6]),(0,[z0,z1,z118,z5,z81,z523])],[(0,[z0,z1,z213,z4,z5,z360]),(0,[z11,z828,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z829,z6]),(1,[z1,z2,z4,z761,z6]),(0,[z287,z1,z4,z5,z59,z6]),(0,[z25,z0,z1,z288,z5,z6]),(0,[z0,z1,z299,z4,z5,z6]),(0,[z0,z1,z44,z4,z5,z256]),(0,[z0,z1,z830,z4,z5,z6]),(0,[z831,z187,z0,z1,z5,z6])],[(0,[z0,z1,z2,z4,z832,z6]),(0,[z0,z33,z4,z338,z5,z6]),(0,[z0,z1,z4,z732,z5,z6]),(0,[z0,z1,z2,z4,z5,z752]),(0,[z32,z0,z1,z120,z2,z5]),(0,[z0,z1,z4,z5,z6,z833])],[(0,[z0,z1,z302,z4,z5,z6]),(0,[z0,z74,z1,z4,z5,z322]),(0,[z1,z2,z4,z5,z761,z6]),(0,[z0,z1,z834,z4,z5,z6]),(0,[z0,z1,z4,z19,z6,z93]),(0,[z0,z835,z1,z4,z5,z6])]],
   [[(0,[z0,z33,z4,z5,z344,z6]),(0,[z0,z775,z2,z4,z5,z6]),(0,[z0,z1,z4,z5,z836,z6]),(0,[z0,z103,z2,z4,z5,z26]),(0,[z0,z1,z837,z4,z5,z6]),(0,[z0,z1,z104,z2,z4,z749])],[(0,[z838,z0,z1,z445,z5,z6]),(0,[z0,z353,z2,z4,z5,z285]),(0,[z1,z22,z4,z5,z6,z459]),(0,[z0,z1,z242,z4,z5,z6]),(0,[z0,z839,z21,z4,z5,z6]),(0,[z337,z0,z203,z4,z5,z6]),(0,[z0,z1,z840,z4,z5,z6]),(0,[z0,z164,z33,z4,z29,z6]),(0,[z25,z841,z1,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z842]),(0,[z0,z1,z2,z4,z207,z749])],[(0,[z0,z1,z843,z4,z5,z6]),(0,[z0,z347,z21,z4,z5,z6]),(0,[z0,z1,z844,z4,z5,z6]),(0,[z0,z1,z2,z845,z5,z6]),(0,[z123,z1,z2,z4,z761,z6])],[(0,[z0,z1,z21,z4,z200,z6]),(0,[z0,z1,z846,z2,z4,z6]),(0,[z25,z0,z1,z4,z5,z329])],[(0,[z1,z21,z847,z4,z5,z6]),(0,[z0,z1,z848,z4,z5,z6]),(0,[z0,z1,z849,z4,z5,z6]),(0,[z0,z850,z33,z4,z5,z6])],[(0,[z0,z1,z255,z4,z5,z6]),(0,[z0,z1,z4,z5,z851,z6]),(0,[z114,z1,z2,z774,z5,z6]),(0,[z0,z852,z1,z4,z5,z6]),(0,[z0,z1,z299,z4,z5,z329])],[(0,[z1,z22,z4,z317,z5,z6]),(0,[z0,z853,z1,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z854]),(0,[z25,z0,z1,z239,z5,z6]),(0,[z0,z77,z1,z4,z19,z6]),(0,[z0,z1,z4,z5,z855,z6]),(0,[z0,z1,z856,z4,z5,z6]),(0,[z0,z762,z2,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6]),(0,[z25,z0,z140,z4,z5,z6]),(0,[z0,z1,z4,z857,z5,z6]),(0,[z0,z1,z2,z858,z5,z6]),(0,[z0,z364,z33,z4,z5,z6]),(0,[z109,z0,z1,z2,z128,z6])]],
   [[(0,[z57,z1,z21,z84,z5,z6]),(0,[z109,z25,z0,z1,z54,z6])],[(0,[z0,z1,z2,z859,z5,z6]),(0,[z0,z1,z860,z4,z5,z6]),(0,[z25,z0,z1,z173,z5,z6]),(0,[z287,z1,z21,z4,z5,z6]),(0,[z0,z1,z861,z4,z5,z6]),(0,[z28,z0,z203,z237,z5,z6]),(0,[z0,z1,z862,z4,z5,z6]),(0,[z0,z1,z2,z863,z5,z6]),(0,[z0,z1,z4,z5,z6,z864]),(0,[z0,z1,z2,z4,z6,z865])],[(0,[z0,z1,z312,z4,z5,z285]),(0,[z0,z1,z4,z5,z6,z866]),(0,[z0,z1,z4,z5,z6,z867]),(0,[z868,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z749,z37])],[(0,[z138,z166,z33,z4,z5,z6]),(0,[z158,z0,z1,z33,z5,z6]),(0,[z0,z1,z2,z4,z869,z6]),(0,[z531,z0,z2,z39,z5,z6])],[(0,[z1,z390,z22,z4,z5,z6]),(0,[z0,z22,z4,z764,z5,z6]),(0,[z584,z1,z22,z4,z5,z6]),(0,[z0,z870,z2,z4,z5,z6]),(0,[z25,z0,z1,z141,z5,z6]),(0,[z32,z0,z1,z5,z320,z206])],[(0,[z0,z1,z871,z4,z5,z6]),(0,[z872,z0,z1,z4,z5,z6]),(0,[z25,z0,z1,z162,z5,z6])],[(0,[z838,z0,z1,z4,z5,z6]),(0,[z0,z1,z873,z4,z5,z6]),(0,[z0,z1,z874,z4,z5,z6]),(0,[z0,z1,z13,z4,z732,z6])]],
   [[(0,[z0,z140,z95,z4,z5,z6]),(0,[z875,z0,z1,z4,z5,z6]),(0,[z0,z156,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z876]),(0,[z0,z1,z104,z121,z4,z37])],[(0,[z0,z1,z2,z877,z5,z6]),(0,[z0,z228,z21,z4,z5,z6]),(0,[z0,z878,z1,z4,z5,z6]),(0,[z25,z0,z1,z508,z5,z6])],[(0,[z160,z1,z21,z4,z5,z6]),(0,[z158,z0,z1,z4,z5,z6]),(0,[z0,z1,z879,z4,z5,z6]),(0,[z0,z1,z4,z729,z5,z6]),(0,[z25,z0,z12,z4,z216,z6]),(0,[z0,z1,z4,z5,z6,z880])],[(0,[z0,z2,z4,z39,z5,z285]),(0,[z0,z2,z622,z39,z5,z6]),(0,[z0,z1,z881,z4,z5,z6]),(0,[z25,z0,z1,z278,z5,z6]),(0,[z0,z1,z33,z882,z5,z6]),(0,[z0,z1,z883,z4,z5,z6])],[(0,[z0,z353,z2,z4,z5,z6]),(0,[z138,z166,z21,z4,z5,z6]),(0,[z25,z0,z1,z281,z5,z6]),(0,[z123,z1,z33,z4,z59,z6]),(0,[z25,z0,z347,z4,z5,z6]),(0,[z25,z0,z1,z52,z5,z6]),(0,[z0,z1,z4,z5,z884,z6])],[(0,[z0,z1,z33,z445,z5,z6]),(0,[z96,z1,z22,z4,z30,z6]),(0,[z169,z0,z778,z4,z5,z6]),(0,[z0,z742,z2,z4,z5,z6]),(0,[z0,z1,z885,z4,z5,z6]),(0,[z0,z1,z2,z886,z5,z6]),(0,[z0,z2,z4,z739,z5,z6]),(0,[z25,z0,z1,z79,z80,z6]),(1,[z0,z1,z4,z5,z752]),(0,[z0,z1,z88,z2,z79,z4])],[(0,[z25,z0,z1,z4,z200,z6]),(0,[z0,z1,z887,z4,z5,z6])],[(0,[z0,z1,z22,z316,z5,z6]),(0,[z114,z1,z21,z58,z5,z6]),(0,[z0,z95,z4,z197,z5,z6]),(0,[z108,z0,z24,z39,z5,z6]),(0,[z0,z23,z2,z4,z5,z721])]],
   [[(0,[z0,z1,z21,z888,z5,z6]),(0,[z199,z25,z0,z1,z5,z6]),(0,[z25,z0,z1,z729,z5,z6]),(0,[z0,z889,z1,z4,z5,z6])],[(0,[z1,z847,z2,z4,z5,z6]),(0,[z1,z58,z4,z405,z5,z6]),(0,[z0,z890,z2,z4,z5,z6]),(0,[z0,z891,z2,z4,z5,z6]),(0,[z0,z1,z120,z2,z118,z4]),(0,[z0,z2,z4,z5,z892,z6])],[(0,[z0,z1,z893,z4,z5,z6]),(0,[z0,z1,z894,z4,z5,z6])],[(0,[z0,z1,z33,z4,z151,z6]),(0,[z25,z0,z1,z298,z5,z6]),(0,[z0,z1,z895,z4,z5,z6]),(0,[z0,z95,z4,z764,z5,z6]),(0,[z1,z134,z21,z4,z5,z6]),(0,[z0,z1,z896,z4,z5,z6]),(0,[z0,z1,z897,z4,z5,z6]),(0,[z898,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z899,z6]),(0,[z0,z900,z2,z4,z5,z6]),(0,[z0,z1,z550,z33,z5,z6]),(0,[z0,z1,z4,z732,z34,z6]),(0,[z0,z1,z2,z4,z6,z369])],[(0,[z0,z1,z21,z445,z5,z6]),(0,[z0,z1,z901,z4,z5,z6]),(0,[z282,z0,z1,z4,z494,z6]),(0,[z0,z1,z902,z2,z4,z6]),(0,[z0,z1,z4,z5,z903,z6])],[(0,[z0,z2,z445,z39,z5,z6]),(0,[z646,z1,z22,z4,z5,z6]),(0,[z437,z1,z22,z4,z5,z6]),(0,[z0,z66,z21,z69,z5,z6]),(0,[z0,z765,z2,z4,z5,z6]),(0,[z60,z1,z2,z84,z5,z6]),(0,[z0,z1,z904,z2,z4,z5]),(0,[z0,z12,z33,z4,z216,z6])],[(0,[z0,z1,z327,z4,z5,z6]),(0,[z57,z100,z1,z84,z5,z6]),(0,[z0,z1,z4,z5,z905,z6]),(0,[z25,z906,z1,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z907,z6]),(0,[z0,z1,z2,z173,z5,z285]),(0,[z0,z1,z2,z4,z5,z908]),(0,[z0,z1,z909,z4,z5,z6]),(0,[z0,z1,z910,z4,z5,z6]),(0,[z0,z1,z2,z911,z5,z6]),(0,[z0,z1,z912,z4,z5,z6]),(0,[z0,z1,z2,z118,z5,z133])],[(1,[z828,z2,z4,z5,z6]),(0,[z0,z1,z22,z719,z5,z6]),(0,[z0,z1,z4,z5,z6,z913]),(0,[z25,z0,z1,z4,z914,z6])],[(0,[z0,z915,z1,z4,z5,z6]),(0,[z0,z1,z22,z118,z5,z81]),(0,[z32,z0,z1,z21,z5,z206]),(0,[z0,z1,z4,z5,z6,z916]),(0,[z168,z287,z1,z4,z5,z6]),(0,[z0,z1,z2,z4,z917,z6]),(0,[z25,z0,z1,z485,z5,z6]),(0,[z0,z918,z2,z4,z5,z6])],[(0,[z0,z1,z334,z4,z5,z6]),(0,[z0,z1,z919,z4,z5,z6])],[(0,[z0,z140,z22,z4,z5,z6]),(0,[z108,z0,z22,z39,z5,z6]),(0,[z0,z2,z4,z5,z6,z920]),(0,[z0,z1,z921,z4,z5,z6]),(0,[z0,z77,z1,z4,z732,z6])],[(0,[z0,z1,z922,z4,z5,z6]),(0,[z0,z1,z923,z4,z5,z6])],[(0,[z184,z828,z2,z4,z5,z6]),(0,[z169,z0,z718,z4,z5,z6]),(0,[z165,z1,z21,z4,z5,z6]),(0,[z0,z1,z924,z4,z5,z6]),(0,[z0,z2,z4,z5,z925,z6]),(0,[z0,z2,z4,z926,z5,z6]),(0,[z0,z103,z2,z4,z5,z721]),(0,[z0,z33,z4,z764,z5,z6]),(0,[z0,z1,z121,z4,z5,z6]),(0,[z0,z1,z2,z5,z801,z206])],[(0,[z0,z1,z2,z4,z5,z927]),(0,[z1,z2,z4,z5,z928,z6]),(0,[z0,z1,z4,z5,z6,z929])]],
   [[(0,[z28,z0,z62,z4,z5,z6]),(0,[z0,z930,z1,z4,z5,z6]),(0,[z0,z1,z4,z882,z5,z6]),(0,[z109,z0,z1,z33,z54,z6]),(0,[z0,z1,z4,z5,z6,z931])],[(0,[z0,z1,z213,z4,z151,z6]),(0,[z109,z0,z1,z22,z54,z6]),(0,[z0,z1,z932,z2,z4,z5]),(0,[z0,z1,z933,z4,z5,z6]),(0,[z934,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z935]),(0,[z11,z184,z145,z4,z5,z6]),(0,[z0,z1,z936,z2,z4,z5]),(0,[z0,z937,z2,z4,z5,z6])],[(0,[z0,z1,z21,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z938]),(0,[z0,z1,z312,z173,z5,z6]),(0,[z0,z1,z2,z939,z5,z6]),(0,[z0,z1,z940,z4,z5,z6])],[(0,[z0,z1,z2,z4,z941,z6]),(0,[z168,z1,z22,z4,z5,z185]),(0,[z0,z1,z4,z5,z942,z6]),(0,[z0,z943,z1,z4,z5,z6]),(0,[z0,z1,z944,z4,z5,z6]),(0,[z1,z2,z4,z5,z793,z27]),(0,[z25,z0,z353,z4,z5,z6]),(0,[z25,z0,z1,z4,z5,z945]),(0,[z25,z0,z1,z342,z5,z6]),(0,[z0,z1,z104,z35,z4,z37])],[(0,[z0,z1,z2,z4,z200,z285]),(0,[z28,z0,z4,z261,z5,z6]),(0,[z0,z946,z2,z4,z5,z6])],[(0,[z0,z1,z56,z95,z5,z6]),(0,[z25,z0,z4,z5,z344,z6]),(0,[z25,z0,z1,z882,z5,z6]),(0,[z0,z1,z2,z4,z769,z6]),(0,[z109,z0,z1,z88,z2,z5])],[(0,[z0,z1,z2,z947,z5,z6]),(0,[z0,z1,z948,z4,z5,z6]),(0,[z0,z1,z13,z4,z34,z6])]],
   [[(0,[z25,z0,z1,z445,z5,z6]),(0,[z0,z1,z4,z949,z5,z6]),(0,[z0,z258,z2,z4,z5,z6]),(0,[z439,z0,z126,z4,z5,z6]),(0,[z25,z803,z1,z4,z5,z6])],[(0,[z0,z1,z2,z4,z950,z6]),(0,[z0,z100,z1,z69,z5,z6]),(0,[z136,z1,z2,z4,z5,z27]),(0,[z0,z1,z951,z4,z5,z6]),(0,[z0,z952,z33,z4,z5,z6]),(0,[z0,z1,z33,z5,z6,z250]),(0,[z187,z0,z1,z104,z2,z37])],[(0,[z0,z1,z4,z5,z6,z953]),(0,[z0,z1,z954,z4,z5,z6]),(0,[z0,z955,z2,z4,z5,z6]),(0,[z0,z1,z956,z4,z5,z6]),(0,[z0,z1,z957,z4,z5,z6]),(0,[z0,z958,z1,z4,z5,z6])],[(0,[z0,z1,z2,z173,z5,z6]),(0,[z0,z1,z959,z4,z5,z6]),(0,[z0,z188,z1,z4,z5,z179]),(0,[z0,z1,z960,z4,z5,z6]),(0,[z0,z1,z21,z4,z5,z329])],[(0,[z138,z25,z0,z39,z5,z6]),(0,[z25,z0,z1,z91,z5,z6]),(0,[z0,z74,z1,z4,z5,z616]),(0,[z0,z1,z13,z4,z68,z6])],[(0,[z158,z0,z1,z39,z5,z6]),(0,[z0,z1,z174,z4,z5,z624]),(0,[z0,z1,z961,z4,z5,z6]),(0,[z123,z1,z242,z4,z59,z6]),(0,[z0,z1,z203,z316,z5,z6]),(0,[z0,z1,z962,z4,z5,z6]),(0,[z0,z1,z2,z963,z5,z6])],[(0,[z25,z0,z1,z4,z151,z6]),(0,[z0,z1,z2,z964,z5,z6]),(0,[z965,z0,z1,z4,z5,z6]),(0,[z214,z0,z62,z4,z5,z6]),(0,[z286,z1,z22,z4,z5,z6]),(0,[z96,z1,z2,z4,z761,z6]),(0,[z0,z966,z1,z4,z5,z6]),(0,[z0,z1,z967,z4,z5,z6]),(0,[z0,z1,z233,z4,z5,z6]),(0,[z0,z968,z2,z4,z5,z6]),(0,[z0,z969,z2,z4,z5,z6])],[(0,[z0,z1,z336,z4,z5,z6]),(0,[z970,z0,z1,z4,z5,z6])]],
   [[(0,[z0,z1,z312,z4,z200,z6]),(0,[z0,z12,z2,z4,z151,z6]),(0,[z0,z1,z4,z5,z6,z971]),(0,[z25,z0,z1,z5,z181,z6]),(0,[z0,z1,z2,z972,z5,z6]),(0,[z831,z0,z1,z4,z5,z6]),(0,[z0,z325,z1,z4,z5,z6]),(0,[z0,z1,z2,z769,z54,z6]),(0,[z0,z1,z4,z973,z5,z6])],[(1,[z1,z847,z4,z5,z6]),(0,[z245,z287,z1,z4,z5,z6]),(1,[z1,z2,z774,z5,z6]),(0,[z96,z1,z33,z4,z30,z6]),(0,[z25,z108,z0,z39,z5,z6]),(0,[z32,z0,z1,z2,z5,z801])],[(0,[z0,z1,z21,z4,z5,z360]),(0,[z0,z22,z4,z714,z5,z6]),(0,[z0,z1,z4,z5,z974,z6]),(0,[z25,z0,z364,z4,z5,z6]),(0,[z0,z1,z13,z4,z182,z6])],[(0,[z975,z0,z1,z4,z5,z6]),(0,[z25,z96,z1,z4,z30,z6]),(0,[z0,z1,z33,z316,z5,z6]),(0,[z0,z1,z2,z4,z5,z976]),(0,[z275,z0,z2,z39,z5,z6]),(0,[z0,z1,z2,z4,z977,z6]),(0,[z345,z0,z155,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z978])],[(0,[z158,z0,z1,z80,z5,z6]),(0,[z0,z1,z22,z237,z5,z6]),(0,[z979,z0,z1,z2,z5,z6]),(0,[z1,z2,z4,z5,z6,z980]),(0,[z25,z0,z228,z4,z5,z6])],[(0,[z0,z981,z1,z4,z5,z6]),(0,[z0,z1,z982,z4,z5,z6]),(0,[z109,z0,z1,z2,z339,z6]),(0,[z0,z1,z4,z5,z6,z983]),(0,[z32,z0,z1,z2,z369,z206])],[(0,[z138,z166,z2,z4,z5,z285]),(0,[z0,z984,z2,z4,z5,z6]),(0,[z0,z839,z2,z4,z5,z6]),(0,[z25,z0,z39,z5,z6,z26]),(0,[z0,z1,z985,z4,z5,z6]),(0,[z0,z986,z2,z4,z5,z6]),(0,[z0,z1,z4,z5,z752,z6]),(0,[z0,z987,z2,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z988])],[(0,[z0,z1,z989,z4,z5,z6]),(0,[z0,z347,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z990,z6]),(0,[z0,z1,z991,z4,z5,z6]),(0,[z646,z1,z2,z4,z59,z6]),(0,[z168,z1,z226,z4,z5,z185]),(0,[z0,z1,z4,z5,z393,z6]),(0,[z0,z1,z992,z4,z5,z6]),(0,[z0,z1,z4,z993,z5,z6]),(0,[z187,z0,z1,z104,z2,z6])]],
   [[(0,[z138,z828,z2,z4,z5,z6]),(0,[z138,z131,z2,z4,z5,z6]),(0,[z25,z0,z103,z4,z5,z26]),(0,[z32,z0,z1,z2,z5,z602])],[(0,[z0,z1,z2,z994,z5,z6]),(0,[z0,z1,z995,z4,z5,z6]),(0,[z11,z184,z22,z4,z5,z6]),(0,[z1,z21,z22,z4,z5,z6]),(0,[z1,z22,z4,z5,z611,z6]),(0,[z1,z22,z4,z612,z5,z6]),(0,[z0,z1,z49,z4,z5,z343]),(0,[z169,z287,z1,z4,z5,z6]),(0,[z0,z1,z4,z5,z996,z6]),(0,[z0,z1,z997,z4,z5,z6]),(0,[z136,z2,z4,z5,z344,z27]),(0,[z0,z74,z1,z4,z5,z14]),(0,[z0,z1,z998,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z999]),(0,[z0,z100,z1,z4,z5,z6]),(0,[z257,z1,z21,z4,z5,z6]),(0,[z267,z1,z4,z405,z5,z6]),(0,[z32,z0,z156,z2,z5,z206])],[(0,[z0,z23,z21,z4,z5,z115]),(0,[z0,z1,z21,z316,z5,z6]),(0,[z0,z1,z2,z4,z761,z6]),(0,[z0,z1,z31,z316,z5,z6]),(0,[z1000,z1,z2,z4,z5,z6]),(0,[z1001,z1,z2,z4,z5,z6]),(0,[z0,z1,z882,z91,z5,z6]),(0,[z1002,z0,z2,z4,z5,z6]),(0,[z187,z0,z1,z2,z207,z6])],[(0,[z169,z0,z1,z69,z5,z6]),(0,[z0,z1,z1003,z4,z5,z6]),(0,[z0,z2,z4,z1004,z5,z6]),(0,[z304,z0,z1,z4,z5,z616]),(0,[z0,z1,z2,z4,z207,z363]),(0,[z0,z1,z2,z5,z6,z801])],[(0,[z0,z1,z21,z79,z80,z6]),(0,[z57,z1,z2,z84,z5,z6]),(0,[z109,z0,z1,z2,z769,z6]),(0,[z0,z1,z359,z4,z6,z369]),(0,[z0,z1005,z2,z4,z5,z6])],[(0,[z0,z1,z1006,z4,z5,z6]),(0,[z25,z0,z1,z227,z5,z6]),(0,[z0,z1,z33,z118,z5,z81]),(0,[z0,z1,z1007,z4,z5,z6])],[(0,[z0,z1,z2,z445,z5,z285]),(0,[z287,z184,z1,z4,z5,z6]),(0,[z0,z805,z22,z4,z5,z6]),(0,[z0,z1,z1008,z4,z5,z6]),(0,[z0,z1,z141,z316,z5,z6]),(0,[z0,z1,z4,z5,z393,z329])]],
   [[(0,[z0,z140,z33,z4,z5,z6]),(0,[z108,z0,z33,z39,z5,z6]),(0,[z0,z1,z4,z5,z6,z320])],[(0,[z138,z166,z312,z4,z5,z6]),(0,[z0,z1,z321,z4,z5,z6]),(0,[z187,z0,z1,z21,z5,z6]),(0,[z0,z1,z2,z1009,z5,z6]),(0,[z0,z224,z2,z4,z216,z6]),(0,[z0,z1,z1010,z4,z5,z6])],[(0,[z0,z1,z1011,z4,z5,z6]),(0,[z245,z1,z847,z4,z5,z6]),(0,[z159,z1,z21,z4,z5,z6]),(0,[z0,z1,z4,z5,z1012,z6]),(0,[z0,z1,z1013,z4,z5,z6]),(0,[z0,z66,z2,z521,z5,z6]),(0,[z109,z0,z1,z88,z2,z54])],[(0,[z158,z0,z1,z91,z5,z6]),(0,[z0,z1,z1014,z4,z5,z6]),(0,[z0,z1,z1015,z4,z5,z6]),(0,[z0,z1,z1016,z4,z5,z6]),(0,[z0,z1017,z2,z4,z5,z6])],[(0,[z0,z22,z4,z197,z5,z6]),(0,[z546,z1,z22,z4,z5,z6]),(0,[z0,z164,z21,z4,z29,z6]),(0,[z0,z716,z21,z4,z5,z6]),(0,[z96,z1,z260,z4,z30,z6]),(0,[z28,z0,z775,z4,z5,z6]),(0,[z0,z1018,z1,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z1019]),(0,[z0,z1,z1020,z4,z5,z6]),(0,[z0,z1,z4,z5,z1021,z6])],[(0,[z0,z1,z1022,z4,z5,z6]),(0,[z25,z0,z1,z4,z5,z360]),(0,[z0,z1,z1023,z4,z5,z6]),(0,[z0,z1,z90,z33,z5,z6]),(0,[z0,z1,z2,z5,z6,z36]),(0,[z0,z1,z1024,z4,z5,z6])],[(0,[z0,z1,z2,z173,z200,z6]),(0,[z0,z228,z2,z4,z5,z6]),(0,[z65,z0,z4,z261,z5,z6]),(0,[z0,z1,z4,z5,z6,z271])],[(0,[z57,z25,z1,z84,z5,z6]),(0,[z0,z1,z1025,z4,z5,z6]),(0,[z25,z0,z1,z368,z5,z6]),(0,[z0,z1,z233,z104,z4,z37])]],
   [[(0,[z108,z0,z21,z39,z5,z6]),(0,[z168,z1,z33,z4,z5,z185]),(0,[z25,z0,z946,z4,z5,z6]),(0,[z187,z0,z1,z33,z5,z6])],[(0,[z187,z0,z1,z22,z5,z6]),(0,[z0,z221,z126,z4,z5,z6]),(0,[z0,z1,z2,z4,z1026,z6]),(0,[z906,z1,z2,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z1027])],[(0,[z0,z1,z312,z445,z5,z6]),(0,[z1028,z0,z1,z173,z5,z6]),(0,[z0,z364,z21,z4,z5,z6]),(0,[z0,z1,z1029,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z1030]),(0,[z0,z2,z4,z5,z721,z6]),(0,[z0,z1,z1031,z4,z5,z6]),(0,[z0,z1,z2,z4,z1032,z6]),(0,[z0,z1,z1033,z4,z5,z6])],[(0,[z25,z0,z1,z423,z5,z6]),(0,[z0,z1,z1034,z4,z5,z6])],[(0,[z0,z1,z1035,z4,z5,z6]),(0,[z0,z103,z22,z4,z5,z26]),(0,[z25,z0,z1,z321,z5,z6]),(0,[z114,z1,z2,z58,z5,z6]),(0,[z187,z0,z1,z2,z48,z5])],[(0,[z0,z1,z2,z4,z5,z285]),(0,[z169,z0,z1,z4,z5,z6]),(0,[z0,z1,z2,z888,z5,z6]),(0,[z25,z0,z937,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1036]),(0,[z0,z1,z1037,z4,z5,z6])],[(0,[z25,z0,z1,z316,z5,z6]),(0,[z0,z1,z1038,z4,z5,z6]),(0,[z25,z0,z1,z4,z1039,z6]),(0,[z0,z1,z4,z5,z6,z1040])],[(0,[z0,z1,z440,z69,z5,z6]),(0,[z25,z0,z1,z104,z4,z37])]],
   [[(0,[z190,z1,z22,z4,z5,z6]),(0,[z0,z1,z1041,z4,z5,z6]),(0,[z1042,z0,z1,z4,z5,z6]),(0,[z0,z699,z2,z4,z29,z6]),(0,[z0,z1,z2,z80,z769,z6])],[(0,[z0,z66,z2,z4,z5,z285]),(0,[z0,z1,z13,z4,z370,z6]),(0,[z0,z1,z2,z1043,z5,z6])],[(0,[z0,z215,z1,z4,z246,z6]),(0,[z1044,z0,z1,z4,z5,z6]),(0,[z0,z1,z2,z4,z798,z6]),(0,[z25,z0,z1,z88,z4,z5]),(0,[z0,z1,z687,z4,z318,z6]),(0,[z1045,z187,z0,z1,z5,z6])],[(0,[z0,z1,z1046,z4,z5,z6]),(0,[z0,z77,z1,z4,z676,z6]),(0,[z0,z66,z2,z69,z5,z6]),(0,[z1047,z1,z2,z4,z5,z6]),(0,[z0,z1,z1048,z4,z5,z6]),(0,[z0,z66,z440,z69,z5,z6]),(0,[z0,z1,z104,z2,z4,z651])],[(0,[z0,z2,z4,z1049,z5,z6]),(0,[z25,z0,z155,z69,z5,z6]),(0,[z0,z1,z104,z33,z4,z37])],[(0,[z1,z22,z4,z684,z5,z6]),(0,[z0,z1,z4,z5,z1050,z6]),(0,[z0,z1,z104,z22,z4,z37]),(0,[z0,z1,z4,z1051,z5,z6]),(0,[z0,z1,z1052,z4,z5,z6]),(0,[z0,z287,z1,z69,z5,z6]),(0,[z25,z0,z1,z4,z5,z711]),(0,[z0,z1,z2,z4,z5,z1053])],[(0,[z0,z1,z2,z1054,z5,z6]),(0,[z828,z166,z2,z4,z5,z6]),(0,[z0,z1,z1055,z4,z5,z6]),(0,[z25,z0,z1,z451,z5,z6]),(0,[z0,z779,z33,z4,z5,z6]),(0,[z0,z1,z1056,z4,z5,z6]),(0,[z32,z0,z1,z2,z5,z206])],[(0,[z138,z166,z2,z173,z5,z6]),(0,[z0,z446,z31,z4,z5,z6]),(0,[z123,z1,z21,z4,z59,z6]),(0,[z0,z1057,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z312,z4,z5,z6]),(0,[z0,z1,z33,z237,z5,z6]),(0,[z0,z1,z120,z33,z4,z6]),(0,[z0,z1,z33,z4,z48,z207])],[(0,[z0,z1,z120,z22,z4,z6]),(0,[z169,z0,z140,z4,z5,z6]),(0,[z25,z0,z1,z505,z5,z6]),(0,[z25,z0,z1,z39,z5,z6]),(0,[z25,z0,z1,z118,z5,z81]),(0,[z0,z1,z1058,z4,z5,z6])],[(0,[z1,z22,z4,z405,z5,z6]),(0,[z0,z1059,z2,z4,z5,z6]),(0,[z0,z1,z1060,z4,z5,z6])],[(0,[z1,z22,z4,z5,z6,z532]),(0,[z0,z1061,z1,z4,z5,z6]),(0,[z0,z1,z1062,z2,z4,z6]),(0,[z0,z1,z1063,z4,z5,z6]),(0,[z108,z0,z219,z39,z5,z6]),(0,[z0,z1,z4,z5,z6,z1064]),(0,[z0,z1,z1065,z4,z5,z6]),(0,[z0,z1,z35,z5,z6,z36])],[(0,[z0,z1066,z1,z4,z5,z6]),(0,[z0,z156,z22,z4,z5,z6]),(0,[z109,z0,z1,z21,z54,z6])],[(0,[z0,z1,z2,z1067,z5,z6]),(0,[z11,z184,z33,z4,z5,z6]),(0,[z0,z100,z1,z39,z5,z6]),(0,[z0,z33,z4,z197,z5,z6]),(0,[z1068,z0,z1,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z1069]),(0,[z0,z664,z2,z4,z5,z26]),(0,[z0,z1,z1070,z4,z5,z6]),(0,[z0,z1071,z1,z4,z5,z6])],[(0,[z0,z1,z21,z4,z151,z6]),(0,[z0,z1,z1072,z4,z5,z6]),(0,[z160,z1,z847,z4,z5,z6]),(0,[z89,z0,z2,z39,z5,z6]),(0,[z0,z219,z1,z4,z5,z6]),(0,[z0,z1,z2,z4,z732,z6]),(0,[z0,z1,z1073,z4,z5,z6]),(1,[z0,z1,z2,z4,z749])],[(0,[z0,z828,z2,z4,z5,z6]),(0,[z123,z2,z4,z338,z59,z6]),(0,[z0,z1,z2,z5,z6,z1074]),(0,[z0,z1,z4,z5,z1075,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z115,z662]),(0,[z0,z353,z22,z4,z5,z6]),(0,[z0,z1,z440,z4,z5,z6]),(0,[z0,z1,z2,z1076,z5,z6]),(0,[z0,z1,z4,z5,z340,z6]),(0,[z0,z1,z2,z4,z5,z801]),(0,[z0,z1,z104,z4,z271,z37])],[(0,[z0,z1,z56,z33,z5,z6]),(0,[z0,z12,z21,z4,z216,z6])],[(0,[z0,z1,z4,z5,z1077,z6]),(0,[z25,z168,z1,z4,z5,z185]),(0,[z1078,z0,z1,z4,z5,z6]),(0,[z0,z1,z1079,z4,z5,z6])],[(0,[z0,z1,z1080,z4,z5,z6]),(0,[z138,z409,z2,z4,z5,z6]),(0,[z0,z1,z1081,z4,z5,z6]),(0,[z0,z1,z1082,z4,z5,z6])],[(0,[z138,z166,z2,z4,z200,z6]),(0,[z0,z1,z2,z1083,z5,z6]),(0,[z0,z1,z1084,z4,z5,z6]),(0,[z474,z0,z2,z39,z5,z6]),(0,[z0,z1,z4,z5,z1085,z6]),(0,[z187,z0,z1,z5,z6,z271])],[(0,[z1086,z0,z1,z4,z5,z6]),(0,[z1,z847,z22,z4,z5,z6]),(0,[z509,z1,z22,z4,z5,z6]),(0,[z0,z1,z813,z2,z4,z6]),(0,[z0,z1,z88,z21,z4,z5]),(0,[z0,z1087,z2,z4,z5,z6]),(0,[z0,z1088,z1,z4,z5,z6]),(0,[z0,z66,z336,z69,z5,z6]),(0,[z0,z77,z1,z4,z376,z6]),(0,[z0,z1,z1089,z4,z5,z6])],[(0,[z0,z1,z2,z173,z151,z6]),(0,[z0,z1,z1090,z4,z5,z6]),(0,[z0,z1,z4,z1091,z5,z6]),(0,[z169,z0,z1,z281,z5,z6]),(0,[z0,z2,z4,z5,z6,z1092]),(0,[z0,z1,z1093,z4,z5,z6]),(0,[z0,z1,z1094,z4,z5,z6]),(0,[z0,z77,z1,z4,z494,z6])],[(0,[z0,z1,z312,z4,z5,z360]),(0,[z0,z1,z932,z22,z4,z5]),(0,[z1,z2,z774,z84,z5,z6]),(0,[z0,z1,z2,z4,z1095,z6]),(0,[z0,z1,z2,z1096,z5,z6]),(0,[z25,z0,z1097,z4,z5,z6]),(0,[z0,z1,z1098,z4,z5,z6]),(0,[z0,z1,z1099,z4,z5,z6])]],
   [[(0,[z1,z95,z4,z405,z5,z6]),(0,[z0,z1,z22,z4,z6,z369]),(0,[z114,z1,z421,z58,z5,z6]),(0,[z0,z1100,z2,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z1101]),(0,[z0,z1,z1102,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z329]),(0,[z32,z0,z1,z359,z5,z206])],[(0,[z11,z2,z4,z5,z575,z6]),(0,[z783,z0,z1,z22,z5,z6]),(0,[z0,z1,z33,z400,z5,z6]),(0,[z0,z140,z861,z4,z5,z6]),(0,[z0,z1,z2,z1103,z5,z6]),(0,[z25,z0,z126,z69,z5,z6]),(0,[z0,z1,z2,z5,z81,z693]),(0,[z1104,z0,z1,z5,z6,z36])],[(0,[z0,z1,z1105,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z1106]),(0,[z0,z1,z24,z237,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1107]),(0,[z0,z1,z1108,z4,z5,z6]),(0,[z1109,z0,z1,z4,z5,z6]),(0,[z123,z347,z2,z4,z59,z6]),(0,[z169,z97,z1,z4,z5,z6]),(0,[z0,z1,z4,z5,z1110,z6])],[(0,[z0,z1,z1111,z4,z5,z6]),(0,[z25,z114,z1,z58,z5,z6]),(0,[z0,z1,z1112,z4,z5,z6]),(0,[z0,z1,z88,z33,z4,z5])],[(0,[z0,z1,z2,z445,z200,z6]),(0,[z0,z1,z1113,z4,z5,z6]),(0,[z0,z1,z88,z22,z4,z5]),(0,[z287,z1,z58,z4,z5,z6]),(0,[z25,z0,z1,z24,z5,z6]),(0,[z1114,z0,z1,z2,z5,z6]),(0,[z0,z1115,z2,z4,z5,z6])],[(0,[z0,z2,z4,z338,z5,z6]),(0,[z0,z1,z2,z5,z708,z6]),(0,[z0,z1,z1116,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z360]),(0,[z0,z2,z4,z5,z115,z285]),(0,[z1,z2,z4,z5,z185,z793])]],
   [[(0,[z0,z2,z4,z5,z344,z6]),(0,[z25,z11,z184,z4,z5,z6]),(0,[z1,z22,z4,z5,z87,z6]),(0,[z169,z0,z1,z39,z5,z6]),(0,[z356,z1,z21,z4,z5,z6]),(0,[z0,z103,z33,z4,z5,z26])],[(0,[z0,z1,z2,z4,z1117,z6]),(0,[z0,z1,z2,z4,z6,z1118]),(0,[z25,z1000,z1,z4,z5,z6])],[(0,[z0,z347,z2,z4,z151,z6]),(0,[z287,z1,z4,z5,z6,z27]),(0,[z0,z1,z2,z739,z5,z6]),(0,[z0,z1,z1119,z4,z5,z6]),(0,[z187,z0,z1005,z2,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1120]),(0,[z0,z1,z1121,z4,z5,z6]),(0,[z0,z1,z1122,z4,z5,z6]),(0,[z0,z2,z4,z1123,z5,z6]),(0,[z0,z1,z1124,z4,z5,z6]),(0,[z0,z221,z31,z4,z5,z6]),(0,[z25,z0,z1,z237,z5,z6]),(0,[z0,z1,z1125,z4,z5,z6]),(0,[z25,z0,z1,z4,z48,z207]),(0,[z0,z1126,z1,z4,z5,z6])],[(0,[z660,z1,z22,z4,z5,z6]),(0,[z96,z1,z334,z4,z30,z6]),(0,[z1127,z0,z1,z4,z5,z6]),(0,[z108,z0,z2,z739,z5,z6]),(0,[z0,z1,z1128,z4,z5,z6]),(0,[z0,z1,z1129,z4,z5,z6])],[(0,[z57,z1,z454,z84,z5,z6]),(0,[z0,z353,z2,z4,z5,z115])],[(0,[z0,z984,z95,z4,z5,z6]),(0,[z0,z1,z4,z318,z34,z6])],[(0,[z0,z1,z847,z4,z5,z6]),(0,[z0,z1,z2,z774,z5,z6]),(0,[z0,z1,z1130,z4,z5,z6]),(0,[z109,z0,z1,z2,z651,z6]),(0,[z0,z1,z104,z2,z36,z37])]],
   [[(0,[z0,z1,z2,z4,z5,z1131]),(0,[z158,z0,z1,z84,z5,z6]),(0,[z0,z103,z21,z4,z5,z26]),(0,[z114,z1,z455,z58,z5,z6]),(0,[z0,z23,z2,z4,z5,z115]),(0,[z25,z0,z1,z375,z5,z6]),(0,[z109,z0,z1,z299,z54,z6])],[(0,[z0,z21,z4,z338,z5,z6]),(0,[z337,z0,z549,z4,z5,z6]),(0,[z0,z1,z2,z1132,z5,z6]),(0,[z0,z1,z4,z5,z6,z1133]),(0,[z187,z0,z1,z104,z2,z4])],[(0,[z0,z1,z21,z845,z5,z6]),(0,[z645,z1,z21,z4,z5,z6]),(0,[z0,z1,z1134,z4,z5,z6]),(0,[z0,z1,z1135,z2,z4,z5]),(0,[z0,z1,z2,z79,z80,z6]),(0,[z32,z0,z1,z120,z2,z4]),(0,[z0,z1,z4,z5,z6,z1136])],[(0,[z0,z1,z2,z4,z200,z6]),(0,[z0,z21,z4,z5,z344,z6]),(0,[z32,z0,z1,z120,z2,z6])],[(0,[z1137,z0,z1,z4,z5,z6]),(0,[z0,z258,z22,z4,z5,z6]),(0,[z0,z1,z421,z4,z5,z6]),(0,[z96,z1,z21,z4,z30,z6]),(0,[z0,z1138,z2,z4,z5,z6]),(0,[z25,z0,z1,z261,z5,z6])],[(0,[z0,z1,z2,z173,z5,z360]),(0,[z0,z1,z2,z4,z1139,z6]),(0,[z136,z1,z22,z4,z5,z27]),(0,[z97,z1,z21,z4,z5,z6]),(0,[z1140,z0,z1,z4,z5,z6]),(0,[z1141,z0,z1,z4,z5,z6]),(0,[z0,z203,z775,z4,z5,z6]),(0,[z0,z1,z1142,z4,z5,z6]),(0,[z0,z1,z1143,z4,z5,z6])],[(0,[z138,z166,z2,z445,z5,z6]),(0,[z0,z1,z2,z4,z1144,z6]),(0,[z1,z2,z4,z774,z5,z6]),(0,[z0,z1,z90,z882,z5,z6]),(0,[z0,z1,z2,z5,z81,z801]),(0,[z0,z1,z2,z4,z5,z749])],[(0,[z0,z1,z22,z173,z5,z6]),(0,[z1028,z0,z1,z4,z5,z6]),(0,[z245,z1,z22,z4,z5,z6]),(0,[z0,z1,z1145,z4,z5,z6]),(0,[z25,z0,z1,z387,z5,z6]),(0,[z0,z1,z33,z137,z5,z6]),(0,[z0,z1,z5,z6,z36,z1136])]],
   [[(0,[z1,z422,z21,z4,z5,z6]),(0,[z491,z1,z2,z4,z30,z6]),(0,[z1146,z0,z1,z4,z5,z6]),(0,[z0,z156,z33,z4,z5,z6])],[(0,[z0,z1,z49,z4,z5,z46]),(0,[z0,z753,z2,z4,z5,z6]),(0,[z0,z1,z1147,z4,z5,z6]),(0,[z0,z1,z4,z5,z1148,z6]),(0,[z28,z0,z203,z4,z5,z6]),(0,[z0,z164,z2,z4,z597,z6]),(0,[z0,z164,z2,z4,z29,z6]),(0,[z25,z1149,z1,z4,z5,z6]),(0,[z0,z1,z88,z299,z4,z5])],[(0,[z138,z287,z1,z4,z5,z6]),(0,[z0,z1,z1150,z4,z5,z6]),(0,[z0,z1,z2,z755,z5,z6]),(0,[z0,z1,z4,z5,z6,z1151]),(0,[z403,z1,z21,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1152]),(0,[z0,z1153,z2,z4,z5,z6]),(0,[z0,z1,z1154,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1155]),(0,[z0,z191,z431,z4,z5,z6]),(0,[z0,z140,z919,z4,z5,z6]),(0,[z0,z66,z2,z7,z5,z6]),(0,[z0,z2,z4,z798,z216,z6]),(0,[z0,z1,z1156,z4,z5,z6]),(0,[z0,z1,z4,z19,z163,z6]),(0,[z1157,z0,z1,z2,z5,z6]),(1,[z109,z0,z1,z88,z2]),(0,[z109,z0,z1,z2,z329,z54]),(1,[z32,z0,z1,z120,z2])],[(0,[z11,z184,z3,z4,z5,z6]),(0,[z0,z1,z1158,z4,z5,z6]),(0,[z1159,z0,z1,z2,z5,z6]),(0,[z0,z353,z33,z4,z5,z6]),(0,[z0,z850,z2,z4,z5,z6]),(0,[z109,z0,z1,z393,z54,z6]),(0,[z1104,z0,z1,z4,z5,z6])],[(0,[z0,z1,z1160,z4,z5,z6]),(0,[z136,z1,z70,z4,z5,z27]),(0,[z0,z1,z1161,z4,z5,z6]),(0,[z0,z1,z1162,z4,z5,z6]),(0,[z0,z1,z2,z4,z1163,z6])],[(0,[z0,z1,z2,z4,z914,z6]),(0,[z0,z1,z79,z80,z340,z6])],[(0,[z168,z1,z327,z4,z5,z185]),(0,[z627,z1,z2,z4,z5,z185]),(0,[z25,z0,z1,z489,z5,z6]),(0,[z0,z364,z2,z4,z5,z6]),(0,[z25,z0,z1,z407,z5,z6]),(0,[z0,z1,z33,z5,z6,z638])]],
   [[(0,[z0,z1,z2,z4,z151,z285]),(0,[z1,z828,z2,z4,z5,z6]),(0,[z25,z11,z0,z39,z5,z6])],[(0,[z0,z1,z301,z4,z370,z6]),(0,[z0,z1,z21,z118,z5,z81]),(0,[z123,z1,z101,z4,z59,z6]),(0,[z25,z0,z1,z577,z5,z6]),(0,[z0,z1,z1164,z4,z5,z6]),(0,[z0,z1,z359,z4,z5,z6]),(0,[z0,z1,z33,z5,z477,z6])],[(0,[z0,z1,z2,z4,z200,z360]),(0,[z0,z984,z22,z4,z5,z6]),(0,[z0,z1,z1165,z4,z5,z6]),(0,[z109,z0,z258,z2,z54,z6])],[(0,[z0,z1,z2,z4,z5,z1166]),(0,[z0,z347,z22,z4,z5,z6]),(0,[z0,z1,z22,z4,z990,z6]),(0,[z0,z1,z2,z4,z780,z5]),(0,[z0,z140,z21,z4,z5,z6]),(0,[z25,z0,z4,z197,z5,z6]),(0,[z0,z1,z1167,z4,z5,z6]),(0,[z1168,z0,z1,z4,z5,z6]),(0,[z0,z1,z1169,z4,z5,z6]),(0,[z0,z1,z1170,z4,z5,z6])],[(0,[z138,z166,z2,z4,z5,z6]),(0,[z0,z1,z1171,z4,z5,z6]),(0,[z0,z1,z455,z4,z5,z6]),(0,[z114,z1,z95,z58,z5,z6]),(0,[z1172,z1,z2,z4,z5,z6]),(0,[z0,z1,z33,z4,z6,z369])],[(0,[z1,z21,z172,z4,z5,z6]),(0,[z0,z1,z42,z321,z5,z6]),(0,[z1045,z0,z1,z4,z5,z6])],[(0,[z25,z0,z1,z521,z5,z6]),(0,[z0,z1,z33,z73,z5,z6]),(0,[z0,z1,z1173,z4,z5,z6])],[(0,[z0,z1,z2,z5,z6,z788])]],
   [[(0,[z0,z1,z213,z4,z5,z285]),(0,[z0,z1,z2,z4,z1174,z6]),(0,[z1,z456,z21,z4,z5,z6]),(0,[z0,z1,z104,z21,z4,z37]),(0,[z0,z1,z4,z5,z1175,z6]),(0,[z0,z1,z2,z4,z48,z55])],[(0,[z0,z1,z1176,z4,z5,z6]),(0,[z57,z1,z22,z84,z5,z6]),(0,[z158,z0,z1,z171,z5,z6]),(0,[z1177,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z945])],[(0,[z0,z1178,z2,z4,z5,z6]),(0,[z0,z1179,z2,z4,z5,z6])],[(0,[z0,z1,z312,z4,z151,z6]),(0,[z9,z1,z22,z4,z5,z6]),(0,[z168,z1,z21,z4,z5,z185]),(0,[z0,z1,z2,z882,z5,z6])],[(0,[z0,z1,z120,z21,z4,z6]),(0,[z123,z1,z2,z4,z59,z6]),(0,[z0,z1,z1180,z4,z5,z6]),(0,[z0,z74,z1,z4,z5,z661])],[(0,[z0,z1,z2,z445,z5,z6]),(0,[z0,z1,z1181,z4,z5,z6]),(0,[z0,z852,z4,z197,z5,z6]),(0,[z0,z1063,z4,z197,z5,z6]),(0,[z0,z1,z775,z4,z5,z6]),(0,[z25,z0,z69,z39,z5,z6]),(0,[z0,z1182,z2,z4,z5,z6]),(0,[z32,z0,z364,z2,z5,z206]),(0,[z0,z1,z1183,z4,z5,z6])],[(0,[z290,z1,z22,z4,z5,z6]),(0,[z0,z1184,z2,z4,z5,z6]),(0,[z25,z0,z1,z607,z5,z6]),(0,[z0,z253,z1,z4,z5,z6]),(0,[z0,z325,z1,z118,z5,z81])],[(0,[z0,z215,z1,z4,z19,z6]),(0,[z0,z2,z4,z5,z713,z6])]],
   [[(0,[z1185,z0,z1,z4,z5,z6]),(0,[z0,z1,z101,z4,z5,z6]),(0,[z0,z1,z454,z4,z5,z6]),(0,[z109,z0,z1,z2,z54,z6])],[(0,[z0,z66,z2,z445,z5,z6]),(0,[z0,z1,z22,z5,z6,z36]),(0,[z509,z1,z2,z4,z5,z27]),(0,[z0,z1,z45,z4,z5,z752])],[(0,[z0,z1,z2,z4,z5,z1186]),(0,[z0,z22,z4,z338,z5,z6]),(0,[z0,z228,z22,z4,z5,z6]),(0,[z0,z1,z4,z5,z1187,z6]),(0,[z25,z0,z164,z39,z5,z6]),(1,[z0,z2,z4,z798,z6]),(0,[z0,z1,z4,z5,z6,z523])],[(0,[z0,z1,z2,z4,z151,z6]),(0,[z138,z166,z2,z4,z5,z360]),(0,[z160,z1,z4,z405,z5,z6]),(0,[z0,z461,z1,z4,z5,z322]),(0,[z168,z1,z2,z4,z5,z793]),(0,[z0,z500,z2,z4,z5,z115]),(0,[z25,z0,z39,z5,z216,z6]),(0,[z0,z1,z1188,z4,z5,z6]),(0,[z0,z1,z2,z79,z769,z6]),(0,[z0,z1,z1189,z4,z5,z6])],[(0,[z0,z2,z4,z39,z151,z6]),(0,[z1,z2,z4,z761,z59,z6]),(0,[z96,z287,z1,z4,z5,z6]),(0,[z1,z2,z4,z5,z793,z6]),(0,[z0,z1,z4,z1190,z5,z6]),(0,[z0,z232,z31,z4,z5,z6])],[(0,[z0,z1,z145,z4,z5,z6]),(0,[z0,z347,z2,z4,z216,z6]),(0,[z25,z0,z23,z39,z5,z6]),(0,[z0,z2,z4,z29,z798,z6])],[(0,[z0,z1191,z2,z4,z5,z6]),(0,[z0,z1,z1192,z4,z5,z6]),(0,[z0,z1,z2,z4,z1193,z6]),(0,[z0,z12,z2,z4,z216,z6]),(0,[z1194,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z1195,z5,z6]),(0,[z1196,z1,z2,z4,z5,z6]),(0,[z0,z1,z4,z5,z1197,z6])]],
   [[(0,[z0,z1,z95,z4,z5,z6]),(0,[z114,z1,z22,z58,z5,z6]),(0,[z119,z1,z22,z4,z5,z6]),(0,[z0,z1,z1198,z4,z5,z6]),(0,[z0,z155,z203,z4,z5,z6]),(0,[z0,z1,z1199,z4,z5,z6]),(0,[z841,z1,z2,z4,z5,z6]),(0,[z0,z232,z141,z4,z5,z6]),(0,[z551,z0,z1,z33,z5,z6]),(0,[z0,z258,z33,z4,z5,z6]),(0,[z32,z0,z1,z120,z2,z206])],[(0,[z0,z1,z22,z4,z5,z285]),(0,[z0,z778,z21,z4,z5,z6]),(1,[z1,z2,z4,z5,z793]),(0,[z136,z1,z33,z4,z5,z27])],[(0,[z0,z1,z289,z4,z107,z6]),(0,[z0,z1,z1200,z4,z5,z6]),(0,[z0,z2,z4,z5,z798,z6]),(0,[z0,z1,z4,z5,z6,z1201]),(0,[z0,z1,z392,z4,z5,z46]),(0,[z0,z1,z88,z4,z5,z393])],[(0,[z0,z1,z33,z173,z5,z6]),(0,[z0,z1,z21,z237,z5,z6]),(0,[z1202,z0,z1,z4,z5,z6]),(0,[z25,z0,z66,z69,z5,z6]),(0,[z0,z1,z1203,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z721]),(0,[z0,z1,z1204,z4,z5,z6])],[(0,[z0,z1,z2,z445,z5,z360]),(0,[z32,z158,z0,z1,z5,z6]),(0,[z0,z1,z90,z321,z5,z6]),(0,[z0,z1,z1205,z4,z5,z6]),(1,[z187,z0,z1,z104,z2])],[(0,[z138,z25,z166,z4,z5,z6]),(0,[z0,z1,z120,z4,z6,z320]),(0,[z0,z1,z2,z4,z6,z749])],[(0,[z0,z1,z1206,z4,z5,z6]),(0,[z169,z0,z1,z321,z5,z6]),(0,[z0,z1207,z2,z4,z5,z6]),(0,[z32,z0,z1,z2,z378,z5])],[(0,[z0,z1,z2,z4,z5,z1208]),(0,[z0,z1,z1209,z4,z5,z6]),(0,[z0,z1,z1210,z4,z5,z6]),(0,[z0,z66,z22,z69,z5,z6]),(0,[z0,z1,z24,z4,z5,z6]),(0,[z25,z0,z1,z4,z6,z369])]],
   [[(0,[z0,z1,z1211,z4,z5,z6]),(0,[z11,z184,z21,z4,z5,z6]),(0,[z0,z1,z1212,z4,z5,z6]),(0,[z0,z1213,z1,z4,z5,z6]),(1,[z0,z2,z4,z5,z721])],[(0,[z0,z287,z1,z4,z5,z6]),(0,[z1,z516,z21,z4,z5,z6])],[(0,[z0,z1,z2,z4,z151,z360]),(0,[z0,z1,z4,z5,z1214,z6]),(0,[z0,z1,z2,z5,z6,z1215]),(0,[z0,z1097,z2,z4,z5,z6]),(1,[z0,z1,z882,z5,z6]),(0,[z109,z0,z1,z88,z2,z4])],[(0,[z592,z1,z21,z4,z5,z6]),(0,[z109,z0,z1,z88,z2,z6])],[(0,[z0,z1,z1216,z4,z5,z6]),(0,[z0,z66,z69,z33,z5,z6]),(0,[z0,z1,z1217,z4,z5,z6]),(0,[z0,z1,z1218,z4,z5,z6])],[(0,[z25,z0,z1,z241,z5,z6]),(0,[z0,z1,z1219,z4,z5,z6])],[(0,[z0,z1,z1220,z4,z5,z6]),(0,[z0,z1,z1221,z4,z5,z6]),(0,[z0,z1,z1222,z4,z5,z6]),(0,[z0,z984,z33,z4,z5,z6])],[(0,[z0,z1,z790,z173,z5,z6]),(0,[z0,z1,z321,z84,z5,z6]),(0,[z0,z347,z33,z4,z5,z6]),(0,[z0,z1,z1223,z4,z5,z6]),(0,[z0,z1,z2,z1224,z5,z6]),(1,[z0,z1,z2,z769,z6]),(0,[z0,z1,z4,z6,z320,z369])]],
   [[(0,[z0,z221,z431,z4,z5,z6]),(0,[z243,z1,z21,z4,z5,z6]),(0,[z25,z123,z1,z4,z59,z6]),(0,[z0,z1,z4,z5,z6,z1225]),(0,[z0,z1,z4,z5,z6,z1226]),(0,[z0,z253,z1,z79,z80,z6])],[(0,[z0,z1,z213,z173,z5,z6]),(0,[z138,z589,z2,z4,z5,z6]),(0,[z596,z1,z22,z4,z5,z6]),(0,[z0,z188,z1,z4,z5,z14]),(0,[z0,z1,z2,z4,z5,z1227]),(0,[z0,z1,z1228,z4,z5,z6]),(0,[z0,z952,z2,z4,z5,z6]),(0,[z0,z1229,z2,z4,z5,z6]),(0,[z0,z1,z1230,z4,z5,z6])],[(0,[z0,z1231,z1,z4,z5,z6]),(0,[z187,z0,z1,z104,z2,z5])],[(0,[z0,z1,z1232,z4,z5,z6]),(0,[z158,z0,z1,z58,z5,z6]),(0,[z0,z446,z563,z4,z5,z6]),(0,[z0,z1,z1233,z4,z5,z6]),(0,[z25,z0,z778,z4,z5,z6]),(0,[z0,z1,z45,z4,z5,z389])],[(0,[z0,z1,z22,z4,z5,z6]),(0,[z0,z1,z4,z405,z5,z6]),(0,[z114,z140,z2,z58,z5,z6]),(0,[z0,z1,z1234,z4,z5,z6]),(0,[z0,z1,z2,z1235,z5,z6])],[(0,[z0,z718,z21,z4,z5,z6]),(0,[z57,z1,z33,z84,z5,z6]),(0,[z1236,z0,z1,z4,z5,z6])],[(0,[z158,z0,z1,z69,z5,z6]),(0,[z1237,z0,z1,z4,z5,z6])],[(0,[z0,z1,z2,z4,z1238,z6]),(0,[z0,z1,z1239,z4,z5,z6]),(0,[z0,z1240,z1,z4,z5,z6]),(0,[z0,z140,z2,z69,z5,z6]),(0,[z0,z1,z1241,z4,z5,z6]),(0,[z212,z0,z1,z4,z5,z522]),(0,[z0,z1,z1242,z4,z5,z6]),(0,[z109,z32,z0,z1,z104,z2]),(0,[z0,z1,z2,z79,z6,z582])]],
   [[(0,[z0,z1243,z1,z4,z5,z6]),(1,[z0,z1,z4,z732,z6]),(0,[z1244,z1,z2,z4,z5,z6])],[(0,[z96,z1,z2,z4,z30,z6]),(0,[z0,z66,z2,z739,z5,z6]),(0,[z25,z0,z986,z4,z5,z6]),(0,[z0,z1,z35,z4,z5,z6])],[(0,[z0,z140,z2,z445,z5,z6]),(0,[z0,z1,z1245,z4,z5,z6]),(0,[z114,z2,z58,z197,z5,z6]),(1,[z0,z2,z739,z5,z6])],[(0,[z680,z25,z0,z1,z5,z6]),(0,[z0,z1,z2,z316,z5,z6]),(0,[z0,z775,z31,z4,z5,z6]),(0,[z0,z1,z2,z4,z1039,z6]),(0,[z0,z1017,z33,z4,z5,z6])],[(0,[z0,z1,z2,z1246,z5,z6]),(0,[z0,z1,z70,z4,z5,z6]),(0,[z0,z1,z22,z4,z5,z329]),(0,[z0,z1,z2,z4,z6,z1247]),(0,[z0,z23,z2,z4,z5,z553]),(0,[z0,z1,z4,z5,z1248,z6]),(0,[z1249,z0,z1,z4,z5,z6])],[(0,[z979,z0,z1,z22,z5,z6]),(0,[z0,z1250,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1251]),(0,[z1149,z1,z2,z4,z5,z6]),(0,[z0,z1,z33,z5,z6,z36])],[(0,[z0,z1,z213,z4,z200,z6]),(0,[z0,z1,z1252,z4,z5,z6]),(0,[z0,z1,z1253,z4,z5,z6]),(0,[z438,z287,z1,z4,z5,z6]),(0,[z127,z0,z1,z4,z182,z6]),(0,[z32,z25,z0,z1,z5,z206]),(0,[z0,z228,z33,z4,z5,z6]),(0,[z0,z1,z4,z5,z14,z117])],[(0,[z0,z1,z1254,z4,z5,z6]),(0,[z0,z1,z1255,z4,z5,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 513) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 513).take 519) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1032).take 312) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1344)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [513, 519, 312] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 94).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 94).take 84).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 178).take 78).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [94, 84, 78] = true :=
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

end PEqualNP.Outside.L_meta_40764

theorem PEqualNP.Outside.L_meta_40764 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808384 * 2 ^ 32 + 4274571456) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808384 * 2 ^ 32 + 4274571456) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_40764.solve