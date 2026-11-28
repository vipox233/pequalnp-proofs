import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_46062

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
  Nat.testBit (4277074602 * 2 ^ 32 + 4243126400) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0080812b2036636a#64 ++ 0x200404095901b31b#64 ++ 0xc19187ff207e67ef#64 ++ 0xde0c8c3ff903f33f#64 : BitVec 256),
   (0x222664980d8b85b5#64 ++ 0x41113324c06c5c2d#64 ++ 0x666e64983f8f87ff#64 ++ 0xbb337324c1fc7c3f#64 : BitVec 256),
   (0x087028e042d0a8c1#64 ++ 0x8043814702168546#64 ++ 0xd87078e1c3f1f8fd#64 ++ 0x7ec383c70e1f8fc7#64 : BitVec 256),
   (0x17805701b4015606#64 ++ 0x00bc02b80da00ab0#64 ++ 0x9f807f01fc01ff1c#64 ++ 0xfcfc03f80fe00ff8#64 : BitVec 256),
   (0x5ddb8001fb6c0018#64 ++ 0x02eedc000fdb6000#64 ++ 0x7fff8001fffe001b#64 ++ 0xf3fffc000ffff000#64 : BitVec 256),
   (0x9f7d7ed400000000#64 ++ 0x04fbebf6a0000000#64 ++ 0xbffffffe00000007#64 ++ 0xf5fffffff0000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 4]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [0, 8]⟩, ⟨.and, [2, 7]⟩, ⟨.or, [2, 7]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [12, 5]⟩, ⟨.and, [9, 13]⟩, ⟨.or, [14, 10]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0080812b2036636a 0x200404095901b31b 0xc19187ff207e67ef 0xde0c8c3ff903f33f

def z1 : W := mkw 0x087028e042d0a8c1 0x8043814702168546 0xd87078e1c3f1f8fd 0x7ec383c70e1f8fc7

def z2 : W := mkw 0x17805701b4015606 0x00bc02b80da00ab0 0x9f807f01fc01ff1c 0xfcfc03f80fe00ff8

def z3 : W := mkw 0x222664980d8b85b5 0x41113324c06c5c2d 0x666e64983f8f87ff 0xbb337324c1fc7c3f

def z4 : W := mkw 0x5ddb8001fb6c0018 0x02eedc000fdb6000 0x7fff8001fffe001b 0xf3fffc000ffff000

def z5 : W := mkw 0x5ddb8021fb7c2058 0x02eedc010fdbe102 0xffff80e1fffe60ff 0xfffffc070ffff307

def z6 : W := mkw 0x9f7d7ed400000000 0x04fbebf6a0000000 0xbffffffe00000007 0xf5fffffff0000000

def z7 : W := mkw 0x087028c042c08881 0x8043814602160444 0x18607800c3819810 0x20c303c0061c0cc0

def z8 : W := mkw 0x08f0a9eb62f6ebeb 0xa047854f5b17b75f 0xd9f1ffffe3ffffff 0xfecf8fffff1fffff

def z9 : W := mkw 0x0080010120004202 0x0004000809000210 0x818007012000670c 0xdc0c003809000338

def z10 : W := mkw 0x5d5b8000db6c0018 0x02eadc0006db6000 0x7e7f8000dffe0013 0x23f3fc0006fff000

def z11 : W := mkw 0x37865719bd0b5736 0x41bc32b8cde85ab9 0xbf8e7f19fc0fff1e 0xfdfc73f8cfe07ff8

def z12 : W := mkw 0x2204441804030524 0x41102220c0201829 0x0000041800000700 0x00000020c0000038

def z13 : W := mkw 0x0a707fe046d1fec7 0x805383ff02368ff6 0xd8707fe1c3f1fffd 0x7ec383ff0e1f8fff

def z14 : W := mkw 0x40828001fb6c0018 0x020414000fdb6000 0x40000001fffe0018 0x020000000ffff000

def z15 : W := mkw 0xdffffed5fb6c0018 0x06fffff6afdb6000 0xfffffffffffe001f 0xf7fffffffffff000

def z16 : W := mkw 0x0020208000808081 0x0001010400040404 0x0060600003818010 0x20030300001c0c00

def z17 : W := mkw 0x0000000000000000 0x0000000000000000 0x000004002000070c 0x9800002001000038

def z18 : W := mkw 0x002028e00090a8c1 0x8001014700048546 0x800078e00001f8e4 0x0c0003c700000fc7

def z19 : W := mkw 0x558b8001b92c0018 0x02ac5c000dc96000 0x278f80003c0e0002 0x813c7c0001e07000

def z20 : W := mkw 0x0000002000102040 0x0000000100008102 0xc01000e1007060ed 0x5e00800708038307

def z21 : W := mkw 0x0000000000000000 0x0000000000000000 0x819187fe00000007 0xd40c8c3ff0000000

def z22 : W := mkw 0x9ffdffff2036636a 0x24ffeffff901b31b 0xffffffff207e67ef 0xfffffffff903f33f

def z23 : W := mkw 0x887d28d400000000 0x0443e946a0000000 0x207f80fe00000003 0x0103fc07f0000000

def z24 : W := mkw 0x200200080d8b85b5 0x41001000406c5c2d 0x400000003f8f87f8 0x0a00000001fc7c3f

def z25 : W := mkw 0x82247ed400000000 0x041123f6a0000000 0x80007ffe00000004 0x040003fff0000000

def z26 : W := mkw 0x970d561400000000 0x04b86ab0a0000000 0x278f871e00000002 0x813c7c38f0000000

def z27 : W := mkw 0x22246498048385a5 0x41112324c0241c2d 0x266e6498000187e7 0xb9337324c0000c3f

def z28 : W := mkw 0x0002000009080010 0x0000100000484000 0x666e00003f8e001b 0xb333700001fc7000

def z29 : W := mkw 0x9f7d7ef442d0a8c1 0x84fbebf7a2168546 0xffffffffc3f1f8ff 0xfffffffffe1f8fc7

def z30 : W := mkw 0x1d59000000000000 0x00eac80000000000 0x3fff800000000003 0xf1fffc0000000000

def z31 : W := mkw 0x0080010120004202 0x0004000809000210 0x0000000120006708 0x0800000009000338

def z32 : W := mkw 0x222664900d898495 0x41113324806c4c24 0x266e60001f818010 0x2133730000fc0c00

def z33 : W := mkw 0x0080812b2036636a 0x200404095901b31b 0x818187fe200e67e6 0x8c0c0c3ff100733f

def z34 : W := mkw 0x9d591a4400000000 0x04eac8d220000000 0x99919b6600000000 0x44cc8cdb30000000

def z35 : W := mkw 0x9f7d7ed404010404 0x04fbebf6a0200820 0xbffffffe3c01871f 0xfdfffffff1e00c38

def z36 : W := mkw 0xbf7f7edc0d0b0534 0x45fbfbf6e0685829 0xbffffffe3c0e0707 0xf5fffffff1e07038

def z37 : W := mkw 0x0080812b2036636a 0x200404095901b31b 0x4181871f207e67ea 0x8a0c0c38f903f33f

def z38 : W := mkw 0x0080800120240008 0x0004040009012000 0x41918001207e000b 0xd20c8c000903f000

def z39 : W := mkw 0x5ddb812bfb7e637a 0x22eedc095fdbf31b 0xffff87fffffe67ff 0xfffffc3ffffff33f

def z40 : W := mkw 0x200200080d8b85b5 0x41001000406c5c2d 0x400004983f8f87ff 0x9a000024c1fc7c3f

def z41 : W := mkw 0x578bd701bd2d561e 0x02bc5eb80de96ab0 0xbf8fff01fc0fff1e 0xfdfc7ff80fe07ff8

def z42 : W := mkw 0x9ffdffffb437776e 0x24ffeffffda1bbbb 0xfffffffffc7fffff 0xffffffffffe3ffff

def z43 : W := mkw 0x222664980d8b85b5 0x41113324c06c5c2d 0x266e64981f8187f4 0x29337324c0fc0c3f

def z44 : W := mkw 0x220644180d0b0534 0x41103220c0685829 0x260e64183c0f871e 0xb9307320c1e07c38

def z45 : W := mkw 0x0080810b2026432a 0x2004040859013219 0x0181871e200e0702 0x800c0c38f1007038

def z46 : W := mkw 0x5d5b0000db480010 0x02ead80006da4000 0x3e6e0000df800010 0x21f3700006fc0000

def z47 : W := mkw 0x0000000000000000 0x0000000000000000 0x98001801c0007800 0x44c000c00e0003c0

def z48 : W := mkw 0x17a07fe1b491fec7 0x80bd03ff0da48ff6 0x9f807fe1fc01fffc 0xfcfc03ff0fe00fff

def z49 : W := mkw 0x1700560000000000 0x00b802b000000000 0x9f807f0000000004 0xf4fc03f800000000

def z50 : W := mkw 0x9ffd7fd5b4015606 0x04ffebfeada00ab0 0xbffffffffc01ff1f 0xfdffffffffe00ff8

def z51 : W := mkw 0x5fdbc401ff6d041c 0x02fede200ffb6820 0x7fffe401ffff871f 0xfbffff200ffffc38

def z52 : W := mkw 0x5ddb9301fb6c521a 0x02eedc980fdb6290 0xffff9b01fffe781b 0xf7fffcd80ffff3c0

def z53 : W := mkw 0x0000002000102040 0x0000000100008102 0x40000001007060e8 0x0a00000008038307

def z54 : W := mkw 0x2286c51b2d2f473e 0x61143628d9697a39 0x278f871e3c0e0702 0x813c7c38f1e07038

def z55 : W := mkw 0x222664980d8b85b5 0x41113324c06c5c2d 0x666e60003f8f87f8 0x2b33730001fc7c3f

def z56 : W := mkw 0x087028e042d0a8c1 0x8043814702168546 0x407000e003f000e1 0x02038007001f8007

def z57 : W := mkw 0x17805701b4015606 0x00bc02b80da00ab0 0x078007003c000700 0x803c003801e00038

def z58 : W := mkw 0x0000000800020120 0x0000000040001009 0x40000498200e07ef 0x9a000024c100703f

def z59 : W := mkw 0x7f7f6498dfcb85b5 0x43fbfb24c6fe5c2d 0x7e6e6498ff8f87ff 0xbbf37324c7fc7c3f

def z60 : W := mkw 0x0000012a00126362 0x200000095000931b 0xc00007fe200e67ef 0x9e00003ff100733f

def z61 : W := mkw 0x558b8001b92c0018 0x02ac5c000dc96000 0x679f80013c7e000b 0xd33cfc0009e3f000

def z62 : W := mkw 0x222665ba0d9be7f7 0x6111332dd06cdf3f 0xe66e67fe3f8fe7ff 0xbf33733ff1fc7f3f

def z63 : W := mkw 0x978d5715b4015606 0x04bc6ab8ada00ab0 0x278f871e3c000702 0x813c7c38f1e00038

def z64 : W := mkw 0x0000000000000000 0x0000000000000000 0x98007801c001f81c 0x7cc003c00e000fc0

def z65 : W := mkw 0x1dd01b61f2507a42 0x80ee80db0f9283d2 0x99901b61c0707800 0x44cc80db0e0383c0

def z66 : W := mkw 0x15801301b0005202 0x00ac00980d800290 0x0180030000000000 0x000c001800000000

def z67 : W := mkw 0x5dfba8e1fbfca8d9 0x82efdd470fdfe546 0xfffff8e1fffff8ff 0xffffffc70fffffc7

def z68 : W := mkw 0x0224649000000000 0x0011232480000000 0x266e649800000007 0xb1337324c0000000

def z69 : W := mkw 0xbf7f7edc0d8b85b5 0x45fbfbf6e06c5c2d 0xfffffffe3f8f87ff 0xfffffffff1fc7c3f

def z70 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z71 : W := mkw 0x2224649004818485 0x4111232480240c24 0x0000600000018000 0x0000030000000c00

def z72 : W := mkw 0x222664980d8b85b5 0x41113324c06c5c2d 0x666e04983f8e07e3 0x83337024c1fc703f

def z73 : W := mkw 0x1f707ec000000000 0x00fb83f600000000 0x9ff07fe000000005 0xf4ff83ff00000000

def z74 : W := mkw 0x5fdbd701ff6d561e 0x02fedeb80ffb6ab0 0xffffff01ffffff1f 0xfffffff80ffffff8

def z75 : W := mkw 0x40828001fb6c0018 0x020414000fdb6000 0x666e0001fffe001b 0xb33370000ffff000

def z76 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000049800000007 0x90000024c0000000

def z77 : W := mkw 0x1780d701b425560e 0x00bc06b80da12ab0 0xdf91ff01fc7fff1f 0xfefc8ff80fe3fff8

def z78 : W := mkw 0x0000012a00126362 0x200000095000931b 0x00000000000067e0 0x080000000000033f

def z79 : W := mkw 0x0850000042400000 0x0042800002120000 0x58700001c3f00019 0x72c380000e1f8000

def z80 : W := mkw 0x00800101b4015606 0x000400080da00ab0 0x00000001fc01ff18 0x080000000fe00ff8

def z81 : W := mkw 0x1780d72bb437776e 0x20bc06b95da1bbbb 0xdf91fffffc7fffff 0xfefc8fffffe3ffff

def z82 : W := mkw 0x0000002800122160 0x000000014000910b 0xc01004f9207e67ef 0xde008027c903f33f

def z83 : W := mkw 0x22a66599bd8bd7b7 0x4115332ccdec5ebd 0x666e6499ff8fffff 0xbb337324cffc7fff

def z84 : W := mkw 0x22246498048385a5 0x41112324c0241c2d 0x00006498000187e4 0x08000324c0000c3f

def z85 : W := mkw 0x9f7d7ed442c08881 0x84fbebf6a2160444 0xbffffffec3819817 0xf5fffffff61c0cc0

def z86 : W := mkw 0x5ddb8001fb6c0018 0x02eedc000fdb6000 0xffff87fffffe001f 0xf7fffc3ffffff000

def z87 : W := mkw 0x1700560094011404 0x00b802b004a008a0 0x9f807f00dc019814 0xf4fc03f806e00cc0

def z88 : W := mkw 0x0080812b2036636a 0x200404095901b31b 0x419187fe207e07e3 0x820c8c3ff103f03f

def z89 : W := mkw 0x5ddb8021fbfca8d9 0x82eedc010fdfe546 0x7fff8001fffff8fb 0xfbfffc000fffffc7

def z90 : W := mkw 0xb70f561c0d0b0534 0x45b87ab0e0685829 0x278f871e3c0e0702 0x813c7c38f1e07038

def z91 : W := mkw 0x17825701bd095616 0x00bc12b80de84ab0 0xffee7f01ff8fff1f 0xffff73f80ffc7ff8

def z92 : W := mkw 0xbf7f7efc4fdbadf5 0xc5fbfbf7e27edd6f 0xffffffffffffffff 0xffffffffffffffff

def z93 : W := mkw 0x558b8001b92c0018 0x02ac5c000dc96000 0x67ef80003f8e001b 0xb33f7c0001fc7000

def z94 : W := mkw 0x202220880d8b85b5 0x41011104406c5c2d 0x406060803f8f87fd 0x3a03030401fc7c3f

def z95 : W := mkw 0x400280004b6c0018 0x02001400025b6000 0x4000000003fe0000 0x02000000001ff000

def z96 : W := mkw 0x0080812b2036636a 0x200404095901b31b 0x40000001207e67e8 0x0a0000000903f33f

def z97 : W := mkw 0x00a0a1ab20b6e3eb 0x2005050d5905b71f 0xc1f1e7ff23ffe7ff 0xfe0f8f3ff91fff3f

def z98 : W := mkw 0x200200284fdbadf5 0xc1001001427edd6f 0x40000001fffffff8 0x0a0000000fffffff

def z99 : W := mkw 0x0200560000000000 0x001002b000000000 0x80007f0000000004 0x040003f800000000

def z100 : W := mkw 0x00828001292c0018 0x0004140009496000 0x67ff80013ffe001b 0xf33ffc0009fff000

def z101 : W := mkw 0x22a6e5bb2dbfe7ff 0x6115372dd96dff3f 0xe7ffe7ff3fffe7ff 0xff3fff3ff9ffff3f

def z102 : W := mkw 0x37865719bd0b5736 0x41bc32b8cde85ab9 0x278e07183c0e0702 0x813c7038c1e07038

def z103 : W := mkw 0x02805701b4015606 0x001402b80da00ab0 0x80007f01fc01ff1c 0x0c0003f80fe00ff8

def z104 : W := mkw 0x0000000000000000 0x0000000000000000 0x8180070000000004 0xd40c003800000000

def z105 : W := mkw 0x1700570094015606 0x00b802b804a00ab0 0x9e007f00dc01ff14 0x2cf003f806e00ff8

def z106 : W := mkw 0x0022208009888091 0x00011104004c4404 0x666e60803f8f80ff 0xbb33730401fc7c07

def z107 : W := mkw 0x20262098098a81b1 0x41013104c04c540d 0x606e0098038e00e3 0x03037004c01c7007

def z108 : W := mkw 0x37a67799bd8bd7b7 0x41bd33bccdec5ebd 0xffee7f99ff8fffff 0xffff73fccffc7fff

def z109 : W := mkw 0x20a6a1bb29bee3fb 0x6105350dd94df71f 0xe1ff87ff23fe67ef 0xdf0ffc3ff91ff33f

def z110 : W := mkw 0x0080812b2036636a 0x200404095901b31b 0x40000499207e67ef 0x9a000024c903f33f

def z111 : W := mkw 0x087028c000000000 0x0043814600000000 0x987078e000000005 0x74c383c700000000

def z112 : W := mkw 0x087028c000000000 0x0043814600000000 0x99f1fffe00000007 0xf4cf8ffff0000000

def z113 : W := mkw 0x0080810b2026432a 0x2004040859013219 0x00000000200e0700 0x0000000001007038

def z114 : W := mkw 0x9f7d7ed400000000 0x04fbebf6a0000000 0xbfffffffc001f81f 0xfdfffffffe000fc0

def z115 : W := mkw 0x002028e00090a8c1 0x8001014700048546 0x000000e0000000e0 0x0000000700000007

def z116 : W := mkw 0x22246498048385a5 0x41112324c0241c2d 0x40606498038187fd 0x3a030324c01c0c3f

def z117 : W := mkw 0x0002000009080010 0x0000100000484000 0x266e00001f800010 0x2133700000fc0000

def z118 : W := mkw 0x970d561400000000 0x04b86ab0a0000000 0xbf8fff1e00000006 0xf5fc7ff8f0000000

def z119 : W := mkw 0x0080010120004202 0x0004000809000210 0x8180030100006000 0x440c001808000300

def z120 : W := mkw 0x0870a8ea42f6a9e9 0xa04385475217b54f 0xd871f8ffc3fff8ff 0x7ec38fc7fe1fffc7

def z121 : W := mkw 0x222664b84fdbadf5 0xc1113325c27edd6f 0x666e6499ffffffff 0xbb337324cfffffff

def z122 : W := mkw 0xbf7f7ed40d898495 0x45fbfbf6a06c4c24 0xbffffffe1f818017 0xf5fffffff0fc0c00

def z123 : W := mkw 0x485b80004b6c0018 0x0242dc00025b6000 0x787f8001c3fe001b 0x73c3fc000e1ff000

def z124 : W := mkw 0x7fffe499ffef85bd 0x43ffff24cfff7c2d 0x7fffe499ffff87ff 0xfbffff24cffffc3f

def z125 : W := mkw 0x22a6e59b2dafc7bf 0x6115372cd96d7e3d 0x67efe79e3f8f87ff 0xbb3f7f3cf1fc7c3f

def z126 : W := mkw 0x1700560094011404 0x00b802b004a008a0 0x1e007800dc019810 0x20f003c006e00cc0

def z127 : W := mkw 0x9f7d7ed400000000 0x04fbebf6a0000000 0xbffffb6600000000 0x65ffffdb30000000

def z128 : W := mkw 0x5ddb812bfb7e637a 0x22eedc095fdbf31b 0x7fff8001fffe67fb 0xfbfffc000ffff33f

def z129 : W := mkw 0x9f7d7ed400000000 0x04fbebf6a0000000 0x3e6e780000000000 0x21f373c000000000

def z130 : W := mkw 0x9f7d7ed400000000 0x04fbebf6a0000000 0x9991fffe00000004 0x44cc8ffff0000000

def z131 : W := mkw 0x002028e042d0a8c1 0x8001014702168546 0xc00078e1c3f1f8fc 0x0e0003c70e1f8fc7

def z132 : W := mkw 0x0000802a00362168 0x200004015001b10b 0x401180fe007e00e3 0x02008c07f003f007

def z133 : W := mkw 0x7fffe491ffed849d 0x43ffff248fff6c24 0x7fffe001ffff801b 0xf3ffff000ffffc00

def z134 : W := mkw 0x0000002042d0a8c1 0x8000000102168546 0x40000001c3f1f8f8 0x0a0000000e1f8fc7

def z135 : W := mkw 0x0020208000808081 0x0001010400040404 0x40606080038180fd 0x3a030304001c0c07

def z136 : W := mkw 0x9f5d5e5400000000 0x04faeaf2a0000000 0xbf9f9f7e00000002 0xc5fcfcfbf0000000

def z137 : W := mkw 0x0080812b2036636a 0x200404095901b31b 0xc1800701207e67ec 0xde0c00380903f33f

def z138 : W := mkw 0x0080812bb437776e 0x200404095da1bbbb 0x40000001fc7ffff8 0x0a0000000fe3ffff

def z139 : W := mkw 0x4082812bfb7e637a 0x220414095fdbf31b 0x40000001fffe67f8 0x0a0000000ffff33f

def z140 : W := mkw 0x0000802a00362168 0x200004015001b10b 0x40000000007e00e0 0x020000000003f007

def z141 : W := mkw 0x08f0a9e362f4eacb 0xa047854f1b17a756 0xd9f1fbe7c3f1f8fd 0x7ecf8fdf3e1f8fc7

def z142 : W := mkw 0x20262098098a81b1 0x41013104c04c540d 0x606e6098038f80ff 0x3b037304c01c7c07

def z143 : W := mkw 0x9f7d7ed442400000 0x04fbebf6a2120000 0xffffffffc3f0001f 0xf7fffffffe1f8000

def z144 : W := mkw 0x8a747ed400000000 0x0453a3f6a0000000 0x98707ffe00000005 0x74c383fff0000000

def z145 : W := mkw 0x0000812a0036636a 0x200004095001b31b 0xc01187fe007e67e7 0x0e008c3ff003f33f

def z146 : W := mkw 0x778fc419bd2f053c 0x43bc7e20cde97829 0x278f84183c0e0702 0x813c7c20c1e07038

def z147 : W := mkw 0xdffdfed5f2640008 0x06ffeff6af932000 0xbfffffffc0700007 0xf5fffffffe038000

def z148 : W := mkw 0x1dd9800120240008 0x00eecc0009012000 0x7fff8001207e000b 0xf3fffc000903f000

def z149 : W := mkw 0x0224649000808081 0x0011232480040404 0x666e6498038180ff 0xbb337324c01c0c07

def z150 : W := mkw 0x37a47799b483d7a7 0x41bd23bccda41ebd 0x9f807f99fc01fffc 0xfcfc03fccfe00fff

def z151 : W := mkw 0x5ddb8101fb6c421a 0x02eedc080fdb6210 0xffff8701fffe671f 0xfffffc380ffff338

def z152 : W := mkw 0x2226e4ba0dbfa5fd 0x61113725d06dfd2f 0x667fe4fe3fff87ff 0xbb33ff27f1fffc3f

def z153 : W := mkw 0x2082812b2dbfe7ff 0x61041409596dff3f 0x400000013fffe7f8 0x0a00000009ffff3f

def z154 : W := mkw 0x9ffdfed520240008 0x04ffeff6a9012000 0xffffffff207e000f 0xf7fffffff903f000

def z155 : W := mkw 0x00800121f6d1fec7 0x800400090fb68ff6 0x40000001fff1fff8 0x0a0000000fff8fff

def z156 : W := mkw 0x1780d72bb437776e 0x20bc06b95da1bbbb 0xc79187ff3c7e67ef 0xde3c8c3ff9e3f33f

def z157 : W := mkw 0x0000000000000000 0x0000000000000000 0x4060000003800019 0x32030000001c0000

def z158 : W := mkw 0x0200440004010404 0x0010022000200820 0x9e007c01fc01ff1c 0xfcf003e00fe00ff8

def z159 : W := mkw 0x15801301b0005202 0x00ac00980d800290 0x99801b01c0007800 0x44cc00d80e0003c0

def z160 : W := mkw 0xbf7f7ed40d898495 0x45fbfbf6a06c4c24 0x3e6e78001f818010 0x21f373c000fc0c00

def z161 : W := mkw 0x5d5b0000db480010 0x02ead80006da4000 0x7e7e0001dff00019 0x73f3f0000eff8000

def z162 : W := mkw 0x0200440804030524 0x0010022040201829 0x460064983c0f87ff 0xba300324c1e07c3f

def z163 : W := mkw 0x0850086042502840 0x8042804302128142 0x98101861c0707800 0x44c080c30e0383c0

def z164 : W := mkw 0x2a766cf84fdbadf5 0xc153b367c27edd6f 0xfe7e7cf9ffffffff 0xfff3f3e7cfffffff

def z165 : W := mkw 0x287628f84bdaa9f1 0xc143b147c25ed54f 0x607e00f803fe00e3 0x0303f007c01ff007

def z166 : W := mkw 0x008081232034624a 0x200404091901a312 0xc1918367207e600b 0xd60c8c1b3903f300

def z167 : W := mkw 0x37a6f7bbbdbff7ff 0x61bd37bdddedffbf 0xffffffffffffffff 0xffffffffffffffff

def z168 : W := mkw 0xaa7f6cdc0d8b85b5 0x4553fb66e06c5c2d 0x667fe4fe3f8f87ff 0xbb33ff27f1fc7c3f

def z169 : W := mkw 0x0a746cf042d0a8c1 0x8053a36782168546 0xfe7e7cf9c3f1f8ff 0xfff3f3e7ce1f8fc7

def z170 : W := mkw 0x0000000800020120 0x0000000040001009 0x00000498000007e4 0x08000024c000003f

def z171 : W := mkw 0xdf7f7ed4db480010 0x06fbfbf6a6da4000 0xbffffffedf800017 0xf5fffffff6fc0000

def z172 : W := mkw 0x6a7fe4984fef85bd 0x4353ff24c27f7c2d 0x667fe4983fff87ff 0xbb33ff24c1fffc3f

def z173 : W := mkw 0x087028e042d0a8c1 0x8043814702168546 0xd87078e003f000e5 0x76c383c7001f8007

def z174 : W := mkw 0x9f7d7ef442d0a8c1 0x84fbebf7a2168546 0xfe7e78e1c3f1f8fd 0x7ff3f3c70e1f8fc7

def z175 : W := mkw 0x1724769000000000 0x00b923b480000000 0xbfee7f9800000007 0xf5ff73fcc0000000

def z176 : W := mkw 0x15801301b4015606 0x00ac00980da00ab0 0x99801b01fc01ff18 0x4ccc00d80fe00ff8

def z177 : W := mkw 0x5ddb8009fb6e0138 0x02eedc004fdb7009 0x7fff8499fffe07ff 0xfbfffc24cffff03f

def z178 : W := mkw 0x9f7f7ed409080010 0x04fbfbf6a0484000 0xfffffffe3f8e001f 0xf7fffffff1fc7000

def z179 : W := mkw 0x5dfba9ebfbfeebfb 0xa2efdd4f5fdff75f 0xffffffffffffffff 0xffffffffffffffff

def z180 : W := mkw 0x0080000120000000 0x0004000009000000 0x0180000120000008 0xd00c000009000000

def z181 : W := mkw 0x222664980d8b85b5 0x41113324c06c5c2d 0xe7ffe7fe3f8f87ff 0xff3fff3ff1fc7c3f

def z182 : W := mkw 0x0000000000000000 0x0000000000000000 0x800078000001f804 0x0c0003c000000fc0

def z183 : W := mkw 0x0080010120004202 0x0004000809000210 0x819187ff2000670f 0xdc0c8c3ff9000338

def z184 : W := mkw 0x0080010120004202 0x0004000809000210 0x99807f01e001ff1c 0xfccc03f80f000ff8

def z185 : W := mkw 0x1f707ec0d6c19c85 0x80fb83f606b60ce4 0x1e607800df819810 0x20f303c006fc0cc0

def z186 : W := mkw 0x5dfba8e1fbfca8d9 0x82efdd470fdfe546 0x7fff80e1fffe00fb 0xf3fffc070ffff007

def z187 : W := mkw 0x0000000000000000 0x0000000000000000 0x001180fe00000003 0x00008c07f0000000

def z188 : W := mkw 0x0000012a00126362 0x200000095000931b 0x800007fe000067e4 0x0c00003ff000033f

def z189 : W := mkw 0x0224649800020120 0x00112324c0001009 0x666e6498200e07ef 0xbb337324c100703f

def z190 : W := mkw 0x7fffecf9ffffadfd 0xc3ffff67cffffd6f 0xfffffcf9ffffffff 0xffffffe7cfffffff

def z191 : W := mkw 0x9f7d7ef400102040 0x04fbebf7a0008102 0xffffffff007060ef 0xfffffffff8038307

def z192 : W := mkw 0x0000000000000000 0x0000000000000000 0x18007800c0019810 0x20c003c006000cc0

def z193 : W := mkw 0x087028e042d0a8c1 0x8043814702168546 0x58607801c3f1f8f8 0x2ac303c00e1f8fc7

def z194 : W := mkw 0x5ddb8001fb6c0018 0x02eedc000fdb6000 0xfffff801fffff81f 0xffffffc00fffffc0

def z195 : W := mkw 0x0200440004010404 0x0010022000200820 0x060064003c01871c 0xb830032001e00c38

def z196 : W := mkw 0xdf7f7ed4db480010 0x06fbfbf6a6da4000 0x3e6e7800df800010 0x21f373c006fc0000

def z197 : W := mkw 0x970d561400000000 0x04b86ab0a0000000 0xa79f87fe00000007 0xd53cfc3ff0000000

def z198 : W := mkw 0x0000802a00362168 0x200004015001b10b 0x401184fe207e07ef 0x9a008c27f103f03f

def z199 : W := mkw 0x087028c000808081 0x0043814600040404 0xd87078e0038180fd 0x7ec383c7001c0c07

def z200 : W := mkw 0x0000002042d0a8c1 0x8000000102168546 0xd8007801c3f1f8fc 0x7ec003c00e1f8fc7

def z201 : W := mkw 0x5fdbd601ff6d141c 0x02fedeb00ffb68a0 0x7ffff801ffff981b 0xf3ffffc00ffffcc0

def z202 : W := mkw 0x0000002000102040 0x0000000100008102 0xc19187ff007060ef 0xde0c8c3ff8038307

def z203 : W := mkw 0x0000000004010404 0x0000000000200820 0x000000003c018718 0x0800000001e00c38

def z204 : W := mkw 0x5ddb8001fb6c0018 0x02eedc000fdb6000 0x7e6e0001fffe0018 0x23f370000ffff000

def z205 : W := mkw 0x220644180d0b0534 0x41103220c0685829 0x260e04183c0e0702 0x81307020c1e07038

def z206 : W := mkw 0x5dd98001f2640008 0x02eecc000f932000 0x19918001c0700000 0x40cc8c000e038000

def z207 : W := mkw 0x287228e84fdbadf5 0xc1439147427edd6f 0xd87078e1fffffffd 0x7ec383c70fffffff

def z208 : W := mkw 0x0000000000000000 0x0000000000000000 0x8191836600000000 0x440c8c1b30000000

def z209 : W := mkw 0x48db812b6b7e637a 0x2246dc095b5bf31b 0xe1ff87ff23fe67ef 0xdf0ffc3ff91ff33f

def z210 : W := mkw 0x0080812b2036636a 0x200404095901b31b 0x401180ff207e67eb 0x0a008c07f903f33f

def z211 : W := mkw 0x20262098098a81b1 0x41013104c04c540d 0x606e0498238e07ef 0x9b037024c11c703f

def z212 : W := mkw 0x222664900d898495 0x41113324806c4c24 0x666e60003f8f801b 0xb333730001fc7c00

def z213 : W := mkw 0x0000002042502840 0x8000000102128142 0x00000001c0707800 0x000000000e0383c0

def z214 : W := mkw 0x372676909d899495 0x41b933b484ec4ca4 0x3e6e7800df819810 0x21f373c006fc0cc0

def z215 : W := mkw 0x287628f84bdaa9f1 0xc143b147c25ed54f 0xf87e78f9c3fff8ff 0x7fc3f3c7ce1fffc7

def z216 : W := mkw 0x485b80004b6c0018 0x0242dc00025b6000 0x667f80003ffe001b 0xb333fc0001fff000

def z217 : W := mkw 0x485b80004b6c0018 0x0242dc00025b6000 0x607f800003fe0003 0x0303fc00001ff000

def z218 : W := mkw 0x17a47791b4015606 0x00bd23bc8da00ab0 0xbfee7f99fc01ff1f 0xfdff73fccfe00ff8

def z219 : W := mkw 0x0020208000000000 0x0001010400000000 0x0060608000000005 0x3003030400000000

def z220 : W := mkw 0x0200440000000000 0x0010022000000000 0x0600640000000004 0xb030032000000000

def z221 : W := mkw 0x008081032024420a 0x2004040819012210 0x0181830600000000 0x000c0c1830000000

def z222 : W := mkw 0x15800001b0000000 0x00ac00000d800000 0x1f800001fc000018 0xf0fc00000fe00000

def z223 : W := mkw 0x0224649000000000 0x0011232480000000 0x0000649800000004 0x00000324c0000000

def z224 : W := mkw 0x02804501b4015606 0x001402280da00ab0 0x06006401fc01ff1c 0xb83003200fe00ff8

def z225 : W := mkw 0x002028c000808881 0x8001014600040444 0x0000780000019800 0x000003c000000cc0

def z226 : W := mkw 0x008081232034624a 0x200404091901a312 0x8191836700706000 0x440c8c1b38038300

def z227 : W := mkw 0x17805701b4015606 0x00bc02b80da00ab0 0x9f91fffffc01ff1f 0xfcfc8fffffe00ff8

def z228 : W := mkw 0x9d793ac400000000 0x04ebc9d620000000 0x99f1fbe600000005 0x74cf8fdf30000000

def z229 : W := mkw 0x0080812b2036636a 0x200404095901b31b 0xc1918367207e67e8 0x4e0c8c1b3903f33f

def z230 : W := mkw 0x9f7d7ed494011404 0x04fbebf6a4a008a0 0xbffffffedc019817 0xf5fffffff6e00cc0

def z231 : W := mkw 0x17805701b4015606 0x00bc02b80da00ab0 0x1e007801fc01ff18 0x28f003c00fe00ff8

def z232 : W := mkw 0x55898001b0240008 0x02ac4c000d812000 0x0181800000000000 0x000c0c0000000000

def z233 : W := mkw 0x0850000000000000 0x0042800000000000 0x1870000000000001 0x70c3800000000000

def z234 : W := mkw 0x0280d72b2437776e 0x201406b95921bbbb 0xc191ffff207fffef 0xde0c8ffff903ffff

def z235 : W := mkw 0x1780572bb4137766 0x20bc02b95da09bbb 0x9f807ffffc01fffc 0xfcfc03ffffe00fff

def z236 : W := mkw 0x8a7d6cd400000000 0x0453eb66a0000000 0x267fe4fe00000007 0xb133ff27f0000000

def z237 : W := mkw 0x17805601b4011404 0x00bc02b00da008a0 0x1f807801fc019818 0xf0fc03c00fe00cc0

def z238 : W := mkw 0x087028e042d0a8c1 0x8043814702168546 0xd87018e1c3f078e1 0x46c380c70e1f83c7

def z239 : W := mkw 0x087028c042c08881 0x8043814602160444 0x0060000003800000 0x00030000001c0000

def z240 : W := mkw 0x0080800120240008 0x0004040009012000 0x0191800100700000 0x400c8c0008038000

def z241 : W := mkw 0x1ff07fe1f6d1fec7 0x80ff83ff0fb68ff6 0xdff07fe1fff1fffd 0xfeff83ff0fff8fff

def z242 : W := mkw 0x0226649009080010 0x0011332480484000 0x666e64983f8e001f 0xb3337324c1fc7000

def z243 : W := mkw 0x0200440004010404 0x0010022000200820 0x060060001c018010 0x2030030000e00c00

def z244 : W := mkw 0x0200570004015606 0x001002b800200ab0 0x98007f01c001ff1c 0x7cc003f80e000ff8

def z245 : W := mkw 0x0080810b2026432a 0x2004040859013219 0x819187fe200e0707 0xd40c8c3ff1007038

def z246 : W := mkw 0x2026209009888091 0x41013104804c4404 0x206e000003800000 0x01037000001c0000

def z247 : W := mkw 0x1ff0ffebf6f7ffef 0xa0ff87ff5fb7bfff 0xdff1ffffffffffff 0xfeff8fffffffffff

def z248 : W := mkw 0x220644180d0b0534 0x41103220c0685829 0x660e04983c0e07ef 0x9b307024c1e0703f

def z249 : W := mkw 0x222664900d898495 0x41113324806c4c24 0x266e64003f81871c 0xb933732001fc0c38

def z250 : W := mkw 0x1f707ee0d6d1bcc5 0x80fb83f706b68de6 0xde7078e1dff1f8fd 0x7ef383c70eff8fc7

def z251 : W := mkw 0x22246498048385a5 0x41112324c0241c2d 0x40006498200f87ef 0x9a000324c1007c3f

def z252 : W := mkw 0x9dd99b672034624a 0x24eeccdb3901a312 0x99919b6700706000 0x44cc8cdb38038300

def z253 : W := mkw 0x5ffbffe1fffdfedf 0x82ffdfff0fffeff6 0xffffffe1ffffffff 0xffffffff0fffffff

def z254 : W := mkw 0x17805701b4015606 0x00bc02b80da00ab0 0x078067003c01871c 0xb83c033801e00c38

def z255 : W := mkw 0x1ff07fc1b4015606 0x00ff83fe0da00ab0 0x9ff07fe1fc01ff1d 0xfcff83ff0fe00ff8

def z256 : W := mkw 0x558b8001fb6c0018 0x02ac5c000fdb6000 0x678f8001fffe001a 0x833c7c000ffff000

def z257 : W := mkw 0xdfffffd5ff6d561e 0x06fffffeaffb6ab0 0xffffffffffffff1f 0xfffffffffffffff8

def z258 : W := mkw 0x9f7d7ed494011404 0x04fbebf6a4a008a0 0x3e6e7800dc019810 0x21f373c006e00cc0

def z259 : W := mkw 0x1700560000000000 0x00b802b000000000 0x9f91fffe00000007 0xf4fc8ffff0000000

def z260 : W := mkw 0x5d7b28e0dbd8a8d1 0x82ebd94706dec546 0xfe7e78e1dff1f8fd 0x7ff3f3c70eff8fc7

def z261 : W := mkw 0x087028e042d0a8c1 0x8043814702168546 0xd9f1ffffc3f1f8ff 0xfecf8ffffe1f8fc7

def z262 : W := mkw 0x9f7d7ed400000000 0x04fbebf6a0000000 0x3fefff1e00000002 0xa1ff7ff8f0000000

def z263 : W := mkw 0x0080812b2036636a 0x200404095901b31b 0xd991ffffe07fffff 0xfecc8fffff03ffff

def z264 : W := mkw 0x15800001b0000000 0x00ac00000d800000 0x078000003c000000 0x803c000001e00000

def z265 : W := mkw 0x0000000000808081 0x0000000000040404 0x40000000038180f8 0x0a000000001c0c07

def z266 : W := mkw 0x972d7ed400000000 0x04b96bf6a0000000 0xa78ffffe00000006 0x853c7ffff0000000

def z267 : W := mkw 0xdffffef5fbfca8d9 0x86fffff7afdfe546 0xfffffffffffff8ff 0xffffffffffffffc7

def z268 : W := mkw 0x0000000000000000 0x0000000000000000 0x801000e000000005 0x5400800700000000

def z269 : W := mkw 0x972d769400000000 0x04b96bb4a0000000 0x27efe79e00000007 0xb13f7f3cf0000000

def z270 : W := mkw 0xfffffeddffef85bd 0x47fffff6efff7c2d 0xffffffffffff87ff 0xfffffffffffffc3f

def z271 : W := mkw 0xa2267edc0d8b85b5 0x451133f6e06c5c2d 0xe66e7ffe3f8f87ff 0xbf3373fff1fc7c3f

def z272 : W := mkw 0x0000000000000000 0x0000000000000000 0x4010000100700009 0x5200800008038000

def z273 : W := mkw 0x0200570004015606 0x001002b800200ab0 0x80007f000001ff04 0x0c0003f800000ff8

def z274 : W := mkw 0x5dd98123f274624a 0x22eecc091f93a312 0x99918367c0706000 0x44cc8c1b3e038300

def z275 : W := mkw 0x0000802a00362168 0x200004015001b10b 0xc19187fe007e00e7 0xd60c8c3ff003f007

def z276 : W := mkw 0x222664980d8b85b5 0x41113324c06c5c2d 0x400064983f8f87fc 0x0a000324c1fc7c3f

def z277 : W := mkw 0x0000002000102040 0x0000000100008102 0x8010006100706000 0x4400800308038300

def z278 : W := mkw 0x5ddb8001b92c0018 0x02eedc000dc96000 0x3fff80003c0e0003 0xf1fffc0001e07000

def z279 : W := mkw 0x1500120000000000 0x00a8009000000000 0x99801b0000000000 0x44cc00d800000000

def z280 : W := mkw 0xa2247edc048385a5 0x451123f6e0241c2d 0x80007ffe000187e4 0x0c0003fff0000c3f

def z281 : W := mkw 0x9f7d7ed400000000 0x04fbebf6a0000000 0xbe7e78e000000005 0x75f3f3c700000000

def z282 : W := mkw 0x087028c000000000 0x0043814600000000 0x1860780000000000 0x20c303c000000000

def z283 : W := mkw 0x0200570004015606 0x001002b800200ab0 0x86007f003c01ff1c 0xbc3003f801e00ff8

def z284 : W := mkw 0x9f7d7ed442c08881 0x84fbebf6a2160444 0x3e6e7800c3819810 0x21f373c0061c0cc0

def z285 : W := mkw 0x4082812bfb7e637a 0x220414095fdbf31b 0xc19187fffffe67ff 0xde0c8c3ffffff33f

def z286 : W := mkw 0x222465ba0493e7e7 0x6111232dd0249f3f 0x800067fe0001e7e4 0x0c00033ff0000f3f

def z287 : W := mkw 0x0080812b2036636a 0x200404095901b31b 0xc19183ff007e60e3 0x460c8c1ff803f307

def z288 : W := mkw 0x002028e00090a8c1 0x8001014700048546 0xc06078e00381f8fd 0x3e0303c7001c0fc7

def z289 : W := mkw 0x0080812b2036636a 0x200404095901b31b 0xc01000e1207e67ed 0x5e0080070903f33f

def z290 : W := mkw 0x1780d70bb427572e 0x20bc06b85da13ab9 0x0781871e3c0e0702 0x803c0c38f1e07038

def z291 : W := mkw 0x887d28d400000000 0x0443e946a0000000 0xa1ff87fe00000007 0xd50ffc3ff0000000

def z292 : W := mkw 0x220644100d090414 0x4110322080684820 0x260e00001c000000 0x0130700000e00000

def z293 : W := mkw 0x1fd05f61f6517e46 0x80fe82fb0fb28bf2 0x9f907f61fc71ff1c 0xfcfc83fb0fe38ff8

def z294 : W := mkw 0x0080812b62f6ebeb 0xa00404095b17b75f 0xc19187ffe3ffffff 0xde0c8c3fff1fffff

def z295 : W := mkw 0xa87f28dc098a81b1 0x4543f946e04c540d 0x607f80fe038e00e3 0x0303fc07f01c7007

def z296 : W := mkw 0x08f0a8e162f4a8c9 0x804785470b17a546 0xd9f1f8e1e3fff8ff 0xfecf8fc70f1fffc7

def z297 : W := mkw 0x9d7d28d400000000 0x04ebe946a0000000 0x3fff80fe00000003 0xf1fffc07f0000000

def z298 : W := mkw 0xddffa8d5fb6c0018 0x06effd46afdb6000 0x7fff80fffffe001b 0xf3fffc07fffff000

def z299 : W := mkw 0x17805701b4015606 0x00bc02b80da00ab0 0x878007013c00670c 0xdc3c003809e00338

def z300 : W := mkw 0x978d5715b4015606 0x04bc6ab8ada00ab0 0xbf8fff1ffc01ff1e 0xfdfc7ff8ffe00ff8

def z301 : W := mkw 0x087028e042d0a8c1 0x8043814702168546 0xc07078e003f1f8e5 0x0e0383c7001f8fc7

def z302 : W := mkw 0x37a66499bd8b85b5 0x41bd3324cdec5c2d 0x7fee6499ff8f87ff 0xfbff7324cffc7c3f

def z303 : W := mkw 0x887d28f442d0a8c1 0x8443e947a2168546 0xf87ff8ffc3f1f8ff 0x7fc3ffc7fe1f8fc7

def z304 : W := mkw 0x5ddb810bfb6e433a 0x22eedc085fdb7219 0x7fff871ffffe071b 0xf3fffc38fffff038

def z305 : W := mkw 0x0200560004011404 0x001002b0002008a0 0x0000780000019800 0x000003c000000cc0

def z306 : W := mkw 0x7ffff799ffefd7bf 0x43ffffbccfff7ebd 0xffffff99ffffffff 0xfffffffccfffffff

def z307 : W := mkw 0x1580932bb036736a 0x20ac04995d81b39b 0xd9919fffe07e7fef 0xdecc8cffff03f3ff

def z308 : W := mkw 0x9fd95f45b4015606 0x04fecafa2da00ab0 0x9f91ff67fc01ff1c 0xfcfc8ffb3fe00ff8

def z309 : W := mkw 0x7fdfc419ff6f053c 0x43fefe20cffb7829 0x7fff8419fffe071b 0xf3fffc20cffff038

def z310 : W := mkw 0x0002000009080010 0x0000100000484000 0x606e0000038e0003 0x03037000001c7000

def z311 : W := mkw 0x82247ed400000000 0x041123f6a0000000 0x0000780000000000 0x000003c000000000

def z312 : W := mkw 0x5d5b80004b6c0018 0x02eadc00025b6000 0x7fff800003fe0003 0xf3fffc00001ff000

def z313 : W := mkw 0x0000000000000000 0x0000000000000000 0x800007fe00000004 0x0400003ff0000000

def z314 : W := mkw 0x0224649000000000 0x0011232480000000 0xa7ffe7fe00000007 0xf53fff3ff0000000

def z315 : W := mkw 0x9d591a6442502840 0x84eac8d322128142 0x99919b67c0707800 0x44cc8cdb3e0383c0

def z316 : W := mkw 0x9f7d7fd404015606 0x04fbebfea0200ab0 0xbffffffe0001ff07 0xfdfffffff0000ff8

def z317 : W := mkw 0x9ffd7ed5b0000000 0x04ffebf6ad800000 0xbffffffffc00001f 0xf5ffffffffe00000

def z318 : W := mkw 0x0080802b20362168 0x200404015901b10b 0x419180ff207e00eb 0xd20c8c07f903f007

def z319 : W := mkw 0x5ddb0001fb480010 0x02eed8000fda4000 0x3fee0001ff800018 0xf1ff70000ffc0000

def z320 : W := mkw 0x9f7d7ef40090a8c1 0x84fbebf7a0048546 0xbffffffe0001f8e7 0xfdfffffff0000fc7

def z321 : W := mkw 0x88fda9ff2036636a 0x2447ed4ff901b31b 0xe1ff87ff207e67ef 0xdf0ffc3ff903f33f

def z322 : W := mkw 0x1700560094011404 0x00b802b004a008a0 0x060000001c000000 0x0030000000e00000

def z323 : W := mkw 0x087028e042d0a8c1 0x8043814702168546 0x986078e0c381f8f4 0x2cc303c7061c0fc7

def z324 : W := mkw 0x222664980d8b85b5 0x41113324c06c5c2d 0xfe6e7c99ff8fffff 0xfff373e4cffc7fff

def z325 : W := mkw 0x1d7928c000000000 0x00ebc94600000000 0xbffff8e000000007 0xf5ffffc700000000

def z326 : W := mkw 0x578bd701bd2d561e 0x02bc5eb80de96ab0 0x278f87003c0e0702 0x813c7c3801e07038

def z327 : W := mkw 0x202620980d8b85b5 0x41013104c06c5c2d 0x606e00983f8f87fb 0x0b037004c1fc7c3f

def z328 : W := mkw 0xbf7d7edc048385a5 0x45fbebf6e0241c2d 0xbffffffe000187e7 0xfdfffffff0000c3f

def z329 : W := mkw 0x5df9a8e1f2f4a8c9 0x82efcd470f97a546 0xd9f1f8e1c3f1f8fd 0x7ecf8fc70e1f8fc7

def z330 : W := mkw 0x887d28f442d0a8c1 0x8443e947a2168546 0x607f80fe03f000e3 0x0303fc07f01f8007

def z331 : W := mkw 0x0080812b2036636a 0x200404095901b31b 0xc00007ff207e67ec 0x0e00003ff903f33f

def z332 : W := mkw 0x087028e042d0a8c1 0x8043814702168546 0xc07000e103f060ed 0x5e038007081f8307

def z333 : W := mkw 0x1d59000000000000 0x00eac80000000000 0x3e6e000000000000 0x21f3700000000000

def z334 : W := mkw 0x1780d72bb437776e 0x20bc06b95da1bbbb 0xdf807f01fc7ffffc 0xfefc03f80fe3ffff

def z335 : W := mkw 0x5ddb8001fb6c0018 0x02eedc000fdb6000 0x59918001fffe0018 0x42cc8c000ffff000

def z336 : W := mkw 0x9ffd7fd5b4015606 0x04ffebfeada00ab0 0xbfee7f01fc01ff1c 0xfdff73f80fe00ff8

def z337 : W := mkw 0x0000002000102040 0x0000000100008102 0xd81078e1c071f8fd 0x7ec083c70e038fc7

def z338 : W := mkw 0x558b812bb93e637a 0x22ac5c095dc9f31b 0xe79f87ff3c7e67ef 0xdf3cfc3ff9e3f33f

def z339 : W := mkw 0x82247ef40090a8c1 0x841123f7a0048546 0x80007ffe0001f8e4 0x0c0003fff0000fc7

def z340 : W := mkw 0x0850086042502840 0x8042804302128142 0x98107861c071f81c 0x7cc083c30e038fc0

def z341 : W := mkw 0x82247ed400000000 0x041123f6a0000000 0xa66e7ffe00000007 0xb53373fff0000000

def z342 : W := mkw 0x9d591a4400000000 0x04eac8d220000000 0x99919ffe00000007 0xd4cc8cfff0000000

def z343 : W := mkw 0x0000130000005202 0x0000009800000290 0x80001b0000007800 0x040000d8000003c0

def z344 : W := mkw 0x9d591a4400000000 0x04eac8d220000000 0xbfff9b6600000003 0xf5fffcdb30000000

def z345 : W := mkw 0x0080010120004202 0x0004000809000210 0x0180070020000700 0x800c003801000038

def z346 : W := mkw 0x087028c042c08881 0x8043814602160444 0x58607880c38198fd 0x3ac303c4061c0cc7

def z347 : W := mkw 0xdfdfd615fb6c0018 0x06fefeb0afdb6000 0x7fff871ffffe001b 0xf3fffc38fffff000

def z348 : W := mkw 0x2a766cf04fd9acd5 0xc153b367827ecd66 0xfe7e78e1dff1f8fd 0x7ff3f3c70eff8fc7

def z349 : W := mkw 0x22246cf80493ade5 0xc1112367c0249d6f 0x80007cf80001ffe4 0x0c0003e7c0000fff

def z350 : W := mkw 0x40828021fbfca8d9 0x820414010fdfe546 0x40000001fffff8f8 0x0a0000000fffffc7

def z351 : W := mkw 0x5782d701ff6d561e 0x02bc16b80ffb6ab0 0xdf807f01ffffff1c 0xfefc03f80ffffff8

def z352 : W := mkw 0x15809323b034724a 0x20ac04991d81a392 0x99919b67c0707800 0x44cc8cdb3e0383c0

def z353 : W := mkw 0x9f7dfefe00362168 0x24fbeff7f001b10b 0xfffffffe007e00e7 0xf7fffffff003f007

def z354 : W := mkw 0x087029ea42d2ebe3 0xa043814f5216975f 0xd8707fffc3f1fffd 0x7ec383fffe1f8fff

def z355 : W := mkw 0x1df03be1f2d0fac3 0x80ef81df0f9687d6 0xd9f07be1c3f1f8fd 0x7ecf83df0e1f8fc7

def z356 : W := mkw 0x20020008098a81b1 0x41001000404c540d 0x40000000038e00e0 0x02000000001c7007

def z357 : W := mkw 0x0870208042c08081 0x0043810402160404 0x58706081c3f180fd 0x7ac383040e1f8c07

def z358 : W := mkw 0xdddb9a45fb6c0018 0x06eedcd22fdb6000 0xffff9b67fffe001b 0xf7fffcdb3ffff000

def z359 : W := mkw 0x222664900d898495 0x41113324806c4c24 0x666e60801f8180fd 0x3b33730400fc0c07

def z360 : W := mkw 0x0280450124014606 0x0014022809200a30 0x878067013c01e71c 0xfc3c033809e00f38

def z361 : W := mkw 0x5ddb8123fb7c625a 0x22eedc091fdbe312 0xffff8367fffe601b 0xf7fffc1b3ffff300

def z362 : W := mkw 0x1780570120004202 0x00bc02b809000210 0x9f807f012000670c 0xfcfc03f809000338

def z363 : W := mkw 0x37a67799bd8bd7b7 0x41bd33bccdec5ebd 0x67ee67983f8f87ff 0xbb3f733cc1fc7c3f

def z364 : W := mkw 0x15808001b0240008 0x00ac04000d812000 0x5f918001fc7e001b 0xf2fc8c000fe3f000

def z365 : W := mkw 0x372676989d8b95b5 0x41b933b4c4ec5cad 0x7e6e7c98ff8f9fff 0xbbf373e4c7fc7cff

def z366 : W := mkw 0x087028e000102040 0x0043814700008102 0xd87078e1007060ed 0x7ec383c708038307

def z367 : W := mkw 0x0280c52b2437676e 0x201406295921bb3b 0xc791e7ff3c7fe7ff 0xfe3c8f3ff9e3ff3f

def z368 : W := mkw 0x0020208000808081 0x0001010400040404 0xd8607881c381f8fd 0x7ec303c40e1c0fc7

def z369 : W := mkw 0x1f707ee042d0a8c1 0x80fb83f702168546 0xdff07fe1c3f1f8fd 0xfeff83ff0e1f8fc7

def z370 : W := mkw 0x08d0800162640008 0x004684000b132000 0x59f18001e3fe001b 0xf2cf8c000f1ff000

def z371 : W := mkw 0x087028c042c08881 0x8043814602160444 0x987078e0c3819815 0x74c383c7061c0cc0

def z372 : W := mkw 0x9f7d7ef442d0a8c1 0x84fbebf7a2168546 0xfffffffe03f000e7 0xf7fffffff01f8007

def z373 : W := mkw 0x9f7d7edc00020120 0x04fbebf6e0001009 0xfffffffe200e07ef 0xfffffffff100703f

def z374 : W := mkw 0x0002000009080010 0x0000100000484000 0x260e00003c0e0002 0x8130700001e07000

def z375 : W := mkw 0x0850000042400000 0x0042800002120000 0x4070000003f00001 0x02038000001f8000

def z376 : W := mkw 0x887d28d400000000 0x0443e946a0000000 0xb87ff8fe00000007 0x75c3ffc7f0000000

def z377 : W := mkw 0x9f5d561400000000 0x04faeab0a0000000 0x3fff871e00000003 0xf1fffc38f0000000

def z378 : W := mkw 0x15800001b0000000 0x00ac00000d800000 0x19800001c0000000 0x40cc00000e000000

def z379 : W := mkw 0x0080800120240008 0x0004040009012000 0x01818000200e0002 0x800c0c0001007000

def z380 : W := mkw 0x008081232034624a 0x200404091901a312 0xc19183e7007060ed 0x5e0c8c1f38038307

def z381 : W := mkw 0x48d28001fb6c0018 0x024694000fdb6000 0x58700001fffe0019 0x72c380000ffff000

def z382 : W := mkw 0x002028e00090a8c1 0x8001014700048546 0xc01078e10071f8ed 0x5e0083c708038fc7

def z383 : W := mkw 0x802428d400000000 0x04012146a0000000 0x000000fe00000000 0x00000007f0000000

def z384 : W := mkw 0x1780d723b435764e 0x20bc06b91da1abb2 0x9f91ff67fc71ff1c 0xfcfc8ffb3fe38ff8

def z385 : W := mkw 0x15800001b0000000 0x00ac00000d800000 0x9f807801fc01f81c 0xfcfc03c00fe00fc0

def z386 : W := mkw 0x5ddb802bfb7e2178 0x22eedc015fdbf10b 0x7fff80fffffe00fb 0xf3fffc07fffff007

def z387 : W := mkw 0x9f7d7ed400000000 0x04fbebf6a0000000 0x3e6e7c9800000007 0xb1f373e4c0000000

def z388 : W := mkw 0x222664980d8b85b5 0x41113324c06c5c2d 0x606e6498038f87e7 0x0b037324c01c7c3f

def z389 : W := mkw 0x087028c042c08881 0x8043814602160444 0x98607801c381f81c 0x7cc303c00e1c0fc0

def z390 : W := mkw 0x085200004b480010 0x00429000025a4000 0x7e7e0001fffe001b 0xf3f3f0000ffff000

def z391 : W := mkw 0x00800101b0005202 0x000400080d800290 0x00000001c0007800 0x000000000e0003c0

def z392 : W := mkw 0x02a4e5bb2036636a 0x2015272dd901b31b 0xe7ffe7ff207e67ef 0xff3fff3ff903f33f

def z393 : W := mkw 0x7fffe5bbffffe7ff 0x63ffff2ddfffff3f 0xffffe7ffffffe7ff 0xffffff3fffffff3f

def z394 : W := mkw 0x08f0a9eb62f6ebeb 0xa047854f5b17b75f 0xd87078e1e3fffffd 0x7ec383c70f1fffff

def z395 : W := mkw 0x1700560000000000 0x00b802b000000000 0x1e00780000000000 0x20f003c000000000

def z396 : W := mkw 0x08d0812b6276636a 0x204684095b13b31b 0xd9f187ffe3fe67ff 0xfecf8c3fff1ff33f

def z397 : W := mkw 0x0000000000000000 0x0000000000000000 0x40000000200e000b 0x9200000001007000

def z398 : W := mkw 0x002028c000000000 0x0001014600000000 0x800078e000000004 0x040003c700000000

def z399 : W := mkw 0x5ddb8101ff6d561e 0x02eedc080ffb6ab0 0x7fff8001ffffff1b 0xfbfffc000ffffff8

def z400 : W := mkw 0x9ffdfff72034624a 0x24ffefffb901a312 0xbfffffff00706007 0xf5fffffff8038300

def z401 : W := mkw 0x5dd98001f2640008 0x02eecc000f932000 0x59918001e07e000b 0xd2cc8c000f03f000

def z402 : W := mkw 0x5ddb8001fb6c0018 0x02eedc000fdb6000 0x3f9f8001fc7e0002 0xc1fcfc000fe3f000

def z403 : W := mkw 0xdffffed5b92c0018 0x06fffff6adc96000 0xbffffffe3c0e0007 0xf5fffffff1e07000

def z404 : W := mkw 0x1dd9812b2036636a 0x20eecc095901b31b 0xffff87ff207e67ef 0xfffffc3ff903f33f

def z405 : W := mkw 0x1700560000000000 0x00b802b000000000 0x0780070000000000 0x803c003800000000

def z406 : W := mkw 0x1509000000000000 0x00a8480000000000 0x278f800000000002 0x813c7c0000000000

def z407 : W := mkw 0x40828101ff6d561e 0x020414080ffb6ab0 0x40000001ffffff18 0x0a0000000ffffff8

def z408 : W := mkw 0x40808001f2640008 0x020404000f932000 0x00000001c0700000 0x000000000e038000

def z409 : W := mkw 0x0000012a00126362 0x200000095000931b 0x819187fe000067e7 0xdc0c8c3ff000033f

def z410 : W := mkw 0x15800101b4015606 0x00ac00080da00ab0 0x1f800001fc01ff18 0xf8fc00000fe00ff8

def z411 : W := mkw 0x15801301b0005202 0x00ac00980d800290 0x99807b01c001f81c 0x7ccc03d80e000fc0

def z412 : W := mkw 0x77afe499bdaf85bd 0x43bd7f24cded7c2d 0x67efe4983f8f87ff 0xbb3f7f24c1fc7c3f

def z413 : W := mkw 0x9ffd7fd520004202 0x04ffebfea9000210 0xbfffffff2000670f 0xfdfffffff9000338

def z414 : W := mkw 0x087028c000000000 0x0043814600000000 0x007000e000000001 0x0003800700000000

def z415 : W := mkw 0x0000000000000000 0x0000000000000000 0x060000003c000018 0xb030000001e00000

def z416 : W := mkw 0x9f7d7ed400000000 0x04fbebf6a0000000 0x27ff87fe00000003 0x813ffc3ff0000000

def z417 : W := mkw 0x1df028e1f2d0a8c1 0x80ef81470f968546 0xdff078e1fff1f8fd 0xfeff83c70fff8fc7

def z418 : W := mkw 0x087228e04bd8a8d1 0x80439147025ec546 0xfe7e78e1fffff8ff 0xfff3f3c70fffffc7

def z419 : W := mkw 0x62a6e499ffef85bd 0x43153724cfff7c2d 0x666e6499ffff87ff 0xbb337324cffffc3f

def z420 : W := mkw 0x5fdb5701ff495616 0x02fedab80ffa4ab0 0xbfee7f01ff81ff1c 0xfdff73f80ffc0ff8

def z421 : W := mkw 0x0280570124015606 0x001402b809200ab0 0x81807f012001ff0c 0xdc0c03f809000ff8

def z422 : W := mkw 0x487ba8e04bfca8d9 0x8243dd47025fe546 0xf87ff8e1c3fff8ff 0x7fc3ffc70e1fffc7

def z423 : W := mkw 0x7ddb8009ffef85bd 0x43eedc004fff7c2d 0x7fff8001ffff87fb 0xfbfffc000ffffc3f

def z424 : W := mkw 0x17805701b4015606 0x00bc02b80da00ab0 0x9f807b01dc01f810 0x64fc03d80ee00fc0

def z425 : W := mkw 0x2a7664984fcb85b5 0x4153b324c27e5c2d 0x7e7e6499ffff87ff 0xfbf3f324cffffc3f

def z426 : W := mkw 0x5ddb8001fb6c0018 0x02eedc000fdb6000 0x3fef8000ff8e0012 0xa1ff7c0007fc7000

def z427 : W := mkw 0x00202088008281a1 0x000101044004140d 0x40606498238f87ff 0xba030324c11c7c3f

def z428 : W := mkw 0x0080812b62f6ebeb 0xa00404095b17b75f 0x40000001e3fffff8 0x0a0000000f1fffff

def z429 : W := mkw 0x0204441000000000 0x0010222080000000 0x260e041800000002 0x81307020c0000000

def z430 : W := mkw 0x0200572a04137766 0x201002b950209bbb 0x80007ffe0001ffe4 0x0c0003fff0000fff

def z431 : W := mkw 0x9d7d3ad400000000 0x04ebe9d6a0000000 0xb9ff9bfe00000003 0x45cffcdff0000000

def z432 : W := mkw 0x5dd98001f2640008 0x02eecc000f932000 0x1f918001fc700018 0xf0fc8c000fe38000

def z433 : W := mkw 0x558b8001b92c0018 0x02ac5c000dc96000 0x3f8f8001fc0e001a 0xf1fc7c000fe07000

def z434 : W := mkw 0x0080810b2026432a 0x2004040859013219 0x4191871f207e070b 0xd20c8c38f903f038

def z435 : W := mkw 0x3f7f64980d8b85b5 0x41fbfb24c06c5c2d 0x7fffe4983f8f87ff 0xfbffff24c1fc7c3f

def z436 : W := mkw 0x0000012200106242 0x2000000910008312 0x8000036600006000 0x0400001b30000300

def z437 : W := mkw 0x0080812b2036636a 0x200404095901b31b 0x8191877f207e6702 0xc40c8c3bf903f338

def z438 : W := mkw 0x9f7d7ed400808081 0x04fbebf6a0040404 0xfffffffe038180ff 0xfffffffff01c0c07

def z439 : W := mkw 0x48db8001fb6c0018 0x0246dc000fdb6000 0x607f8001fffe001b 0x0303fc000ffff000

def z440 : W := mkw 0x08f029e1f6d1fec7 0x8047814f0fb68ff6 0xd87078e1fff1fffd 0x7ec383c70fff8fff

def z441 : W := mkw 0x222664b80d9ba5f5 0x41113325c06cdd2f 0xe67e64f93fffe7ff 0xff33f327c9ffff3f

def z442 : W := mkw 0x485b00004b480010 0x0242d800025a4000 0x206e000003800000 0x01037000001c0000

def z443 : W := mkw 0xbf7f7edc098a81b1 0x45fbfbf6e04c540d 0xfffffffe038e00e7 0xf7fffffff01c7007

def z444 : W := mkw 0xd78fd615b92c0018 0x06bc7eb0adc96000 0x278f871e3c0e0002 0x813c7c38f1e07000

def z445 : W := mkw 0x2286c53b2d3f677e 0x61143629d969fb3b 0xe79f87ff3c7e67ef 0xdf3cfc3ff9e3f33f

def z446 : W := mkw 0x00800101b4015606 0x000400080da00ab0 0x98007801fc01ff1c 0x7cc003c00fe00ff8

def z447 : W := mkw 0x22a4e5bb24b7e7ef 0x6115272dd925bf3f 0xc191e7ff207fe7ef 0xde0c8f3ff903ff3f

def z448 : W := mkw 0x17805601b0000000 0x00bc02b00d800000 0x9f807f01fc00001c 0xf4fc03f80fe00000

def z449 : W := mkw 0x1ff07fc1f6c1de87 0x80ff83fe0fb60ef4 0x9fe07f01ff81ff1c 0xfcff03f80ffc0ff8

def z450 : W := mkw 0x087028e042d0a8c1 0x8043814702168546 0x407060e003f180fd 0x3a038307001f8c07

def z451 : W := mkw 0x22266498098a81b1 0x41113324c04c540d 0x666e6498038e00e7 0xb3337324c01c7007

def z452 : W := mkw 0x5fdbd72bff7f777e 0x22fedeb95ffbfbbb 0xffffffffffffffff 0xffffffffffffffff

def z453 : W := mkw 0x008081012024420a 0x0004040809012210 0xc1918701207e670f 0xde0c8c380903f338

def z454 : W := mkw 0x222664980d8b85b5 0x41113324c06c5c2d 0x266e64183f8f8712 0xa1337320c1fc7c38

def z455 : W := mkw 0x0220648004818485 0x0011032400240c24 0x466064803f8187fd 0xba33032401fc0c3f

def z456 : W := mkw 0x0000800000240008 0x0000040000012000 0x40118000007e0003 0x02008c000003f000

def z457 : W := mkw 0x0224649000000000 0x0011232480000000 0x266e600000000000 0x2133730000000000

def z458 : W := mkw 0x2a766cd80d8b85b5 0x4153b366c06c5c2d 0xfe7e7cf83f8f87ff 0xfff3f3e7c1fc7c3f

def z459 : W := mkw 0x9dd91b45b0005202 0x04eec8da2d800290 0x99919b67c0007800 0x44cc8cdb3e0003c0

def z460 : W := mkw 0x0000000800020120 0x0000000040001009 0x40000000200e07e8 0x0a0000000100703f

def z461 : W := mkw 0x5ddb8001fb6c0018 0x02eedc000fdb6000 0x67ff80003ffe0003 0x833ffc0001fff000

def z462 : W := mkw 0x20242098008281a1 0x41012104c004140d 0x00000098000000e0 0x00000004c0000007

def z463 : W := mkw 0x17805701b4015606 0x00bc02b80da00ab0 0x1f800701fc000718 0xf0fc00380fe00038

def z464 : W := mkw 0x48f2a8e1fbfca8d9 0x824795470fdfe546 0xd87078e1fffff8fd 0x7ec383c70fffffc7

def z465 : W := mkw 0x008081232034624a 0x200404091901a312 0x0000000100706000 0x0000000008038300

def z466 : W := mkw 0x0850084000000000 0x0042804200000000 0x9810186000000000 0x44c080c300000000

def z467 : W := mkw 0x1780d72b2036636a 0x20bc06b95901b31b 0xdf91ffff207e67ef 0xfefc8ffff903f33f

def z468 : W := mkw 0x7f7f6490dfc98495 0x43fbfb2486fe4c24 0x3e6e6000df818010 0x21f3730006fc0c00

def z469 : W := mkw 0x2af6edfb6fffefff 0xe157b76fdb7fff7f 0xffffffffffffffff 0xffffffffffffffff

def z470 : W := mkw 0x487ba8e04bfca8d9 0x8243dd47025fe546 0x607f80e003fe00e3 0x0303fc07001ff007

def z471 : W := mkw 0x978dd73f2036636a 0x24bc6eb9f901b31b 0xe79f87ff207e67ef 0xdf3cfc3ff903f33f

def z472 : W := mkw 0x978dd71f2026432a 0x24bc6eb8f9013219 0x278f871e200e0702 0x813c7c38f1007038

def z473 : W := mkw 0x1500000000000000 0x00a8000000000000 0x1f80000000000000 0xf0fc000000000000

def z474 : W := mkw 0x087028e842d2a9e1 0x804381474216954f 0xd8707cf9e3ffffff 0xfec383e7cf1fffff

def z475 : W := mkw 0x0080012120106242 0x0004000909008312 0xc19007e1207067ed 0xde0c803f0903833f

def z476 : W := mkw 0x8a747ef442d0a8c1 0x8453a3f7a2168546 0xd8707fffc3f1f8fd 0x7ec383fffe1f8fc7

def z477 : W := mkw 0x17805701b4015606 0x00bc02b80da00ab0 0x07800701fc01ff18 0x883c00380fe00ff8

def z478 : W := mkw 0x0000002000102040 0x0000000100008102 0x401000e0007000e1 0x0200800700038007

def z479 : W := mkw 0x40020000db480010 0x0200100006da4000 0x00000000df800010 0x0000000006fc0000

def z480 : W := mkw 0x08f0a9eb62f6ebeb 0xa047854f5b17b75f 0xc1f187ff23fe67ef 0xde0f8c3ff91ff33f

def z481 : W := mkw 0x17805701b4015606 0x00bc02b80da00ab0 0x87807f003c01ff04 0x8c3c03f801e00ff8

def z482 : W := mkw 0x0080010920024322 0x0004000849001219 0xc1800799200e67ef 0xde0c003cc900733f

def z483 : W := mkw 0x60828009ffef85bd 0x430414004fff7c2d 0x40000001ffff87f8 0x0a0000000ffffc3f

def z484 : W := mkw 0x00020008090a0130 0x0000100040485009 0x666e04983f8e07ff 0xbb337024c1fc703f

def z485 : W := mkw 0x0020208000808081 0x0001010400040404 0x00006080000180e4 0x0800030400000c07

def z486 : W := mkw 0x0000000800020120 0x0000000040001009 0x40000098000e00e3 0x02000004c0007007

def z487 : W := mkw 0xb72f769c0d8b85b5 0x45b97bb4e06c5c2d 0x67efe79e3f8f87ff 0xbb3f7f3cf1fc7c3f

def z488 : W := mkw 0x20820109bd8bd7b7 0x410410084dec5ebd 0x40000001ff8ffff8 0x0a0000000ffc7fff

def z489 : W := mkw 0x08f029e162d0eac3 0x8047814f0b168756 0xd9f07fe1e3f1fffd 0xfecf83ff0f1f8fff

def z490 : W := mkw 0xbfffffff2dbfe7ff 0x65fffffff96dff3f 0xffffffff3fffe7ff 0xfffffffff9ffff3f

def z491 : W := mkw 0x8859084400000000 0x0442c84220000000 0x0011806600000000 0x00008c0330000000

def z492 : W := mkw 0x15801301b0005202 0x00ac00980d800290 0x9f801b01fc007818 0xf4fc00d80fe003c0

def z493 : W := mkw 0x558b810bb92e433a 0x22ac5c085dc97219 0x278f871e3c0e0702 0x813c7c38f1e07038

def z494 : W := mkw 0x17805709b4035726 0x00bc02b84da01ab9 0xdf807f99fc0fffff 0xfefc03fccfe07fff

def z495 : W := mkw 0x00800101b4015606 0x000400080da00ab0 0x81800701fc01ff1c 0xdc0c00380fe00ff8

def z496 : W := mkw 0x0000010a00024322 0x2000000850001219 0x0000071e00000700 0x00000038f0000038

def z497 : W := mkw 0x1d59000000000000 0x00eac80000000000 0xbfff87fe00000007 0xf5fffc3ff0000000

def z498 : W := mkw 0x0a746cd000000000 0x0053a36680000000 0xbe7e7cf800000007 0xf5f3f3e7c0000000

def z499 : W := mkw 0x0000086000102840 0x8000004300008142 0x8000186000007800 0x040000c3000003c0

def z500 : W := mkw 0x0000000094011404 0x0000000004a008a0 0x00000000dc019810 0x0000000006e00cc0

def z501 : W := mkw 0x15801301b0005202 0x00ac00980d800290 0x99801f01e0007f0c 0xdccc00f80f0003f8

def z502 : W := mkw 0x0850002042d0a8c1 0x8042800102168546 0x58700001c3f1f8f9 0x7ac380000e1f8fc7

def z503 : W := mkw 0x0080802120342048 0x000404010901a102 0xc19180e1207e60ef 0xde0c8c070903f307

def z504 : W := mkw 0x17804401b4010404 0x00bc02200da00820 0x1f806401fc01871c 0xf8fc03200fe00c38

def z505 : W := mkw 0x17805721b4117646 0x00bc02b90da08bb2 0xdf907fe1fc71fffd 0xfefc83ff0fe38fff

def z506 : W := mkw 0x9f7d7ef442502840 0x84fbebf7a2128142 0xbfffffffc0707807 0xf5fffffffe0383c0

def z507 : W := mkw 0x15820001b9080010 0x00ac10000dc84000 0x7fee0001ff8e001b 0xf3ff70000ffc7000

def z508 : W := mkw 0x087028e042502840 0x8043814702128142 0x987078e1c0707805 0x74c383c70e0383c0

def z509 : W := mkw 0x0870a8ea42f6a9e9 0xa04385475217b54f 0x407180fe03fe00e3 0x02038c07f01ff007

def z510 : W := mkw 0x087028e042d0a8c1 0x8043814702168546 0x587078e0c3f198f1 0x22c383c7061f8cc7

def z511 : W := mkw 0x9509120400000000 0x04a8489020000000 0x0181830600000000 0x000c0c1830000000

def z512 : W := mkw 0x008081232034624a 0x200404091901a312 0x819187672070670c 0xdc0c8c3b39038338

def z513 : W := mkw 0x0000802200342048 0x200004011001a102 0x0011806600700000 0x00008c0330038000

def z514 : W := mkw 0xdffffffffb7e637a 0x26ffffffffdbf31b 0xfffffffffffe67ff 0xfffffffffffff33f

def z515 : W := mkw 0x22a6e5bb2dbfe7ff 0x6115372dd96dff3f 0x666e64993fffe7ff 0xbb337324c9ffff3f

def z516 : W := mkw 0x0080810b2026432a 0x2004040859013219 0x8181871f200e670e 0xdc0c0c38f9007338

def z517 : W := mkw 0x02207fe00491fec7 0x801103ff00248ff6 0x80007fe00001ffe4 0x0c0003ff00000fff

def z518 : W := mkw 0x4859800042640008 0x0242cc0002132000 0x0011800000700000 0x00008c0000038000

def z519 : W := mkw 0x0000800a00260128 0x2000040050013009 0x0001801e000e0002 0x00000c00f0007000

def z520 : W := mkw 0x400b8000092c0018 0x02005c0000496000 0x200f8000000e0002 0x01007c0000007000

def z521 : W := mkw 0x08d0896b62766b6a 0xa046844b5b13b35b 0xd9919fffe07e7fef 0xdecc8cffff03f3ff

def z522 : W := mkw 0x220244080d8b85b5 0x41101220406c5c2d 0x460064003f8f87fc 0xba30032001fc7c3f

def z523 : W := mkw 0x5dd99301f264520a 0x02eecc980f932290 0x99919b01c0707800 0x44cc8cd80e0383c0

def z524 : W := mkw 0x1d59000000000000 0x00eac80000000000 0x1991800000000000 0x40cc8c0000000000

def z525 : W := mkw 0x5fdbd701ff6d561e 0x02fedeb80ffb6ab0 0x7fff8701fffe071b 0xf3fffc380ffff038

def z526 : W := mkw 0x087028e042d0a8c1 0x8043814702168546 0x981078e1c071f8e4 0x4cc083c70e038fc7

def z527 : W := mkw 0x1780d70bb427572e 0x20bc06b85da13ab9 0x9f81ff1ffc0fff1e 0xfcfc0ff8ffe07ff8

def z528 : W := mkw 0x1500120090001000 0x00a8009004800080 0x18001800c0001800 0x00c000c0060000c0

def z529 : W := mkw 0x0000000000000000 0x0000000000000000 0x800000010000600c 0x5c00000008000300

def z530 : W := mkw 0x82247ffe00126362 0x241123fff000931b 0x80007ffe000067e4 0x0c0003fff000033f

def z531 : W := mkw 0x087028c000000000 0x0043814600000000 0x987078e1c001f81d 0x7cc383c70e000fc0

def z532 : W := mkw 0x1dd90001b0000000 0x00eec8000d800000 0x3fff8001fc00001b 0xf1fffc000fe00000

def z533 : W := mkw 0x0082812b293e637a 0x200414095949f31b 0xe7ff87ff3ffe67ff 0xff3ffc3ff9fff33f

def z534 : W := mkw 0x222664980d8b85b5 0x41113324c06c5c2d 0x666e60981f8f80f3 0x23337304c0fc7c07

def z535 : W := mkw 0x0000010004015606 0x0000000800200ab0 0x000000000001ff00 0x0800000000000ff8

def z536 : W := mkw 0x0000000042c08881 0x8000000002160444 0x00000000c3819810 0x00000000061c0cc0

def z537 : W := mkw 0x0000000000000000 0x0000000000000000 0x18000001c0000018 0x70c000000e000000

def z538 : W := mkw 0x200200080d0b0534 0x4100100040685829 0x000000003c0e0700 0x0000000001e07038

def z539 : W := mkw 0xc87fa8d44b6c0018 0x0643fd46a25b6000 0x607f80fe03fe0003 0x0303fc07f01ff000

def z540 : W := mkw 0x0200440004010404 0x0010022000200820 0x0000640000018704 0x0800032000000c38

def z541 : W := mkw 0x550b000099080010 0x02a8580004c84000 0x260e00001c000000 0x0130700000e00000

def z542 : W := mkw 0x9ffd7fd5b0005202 0x04ffebfead800290 0xbfffffffc0007807 0xf5fffffffe0003c0

def z543 : W := mkw 0x9dd99b6f2036636a 0x24eeccdb7901b31b 0xd9919fff207e67ef 0xdecc8cfff903f33f

def z544 : W := mkw 0x087028e042d0a8c1 0x8043814702168546 0x98707861c3f1f810 0x64c383c30e1f8fc0

def z545 : W := mkw 0x2026a0ba09bea1f9 0x61013505d04df50f 0x607f80fe03fe00e3 0x0303fc07f01ff007

def z546 : W := mkw 0x5d5b0000db480010 0x02ead80006da4000 0x7e6e0000ff8e001b 0xb3f3700007fc7000

def z547 : W := mkw 0x37a67791bd89d697 0x41bd33bc8dec4eb4 0xbfee7f01ff81ff1c 0xfdff73f80ffc0ff8

def z548 : W := mkw 0x5dd98861f2742848 0x82eecc430f93a142 0x99919861c0707800 0x44cc8cc30e0383c0

def z549 : W := mkw 0x20262098098a81b1 0x41013104c04c540d 0x666e00983f8e00fb 0xb3337004c1fc7007

def z550 : W := mkw 0x0000000800020120 0x0000000040001009 0xc19187fe200e07ef 0xde0c8c3ff100703f

def z551 : W := mkw 0x9d793ae442d0a8c1 0x84ebc9d722168546 0xd9f1fbe7c3f1f8fd 0x7ecf8fdf3e1f8fc7

def z552 : W := mkw 0x1fd95701b4015606 0x00fecab80da00ab0 0xbfffff01fc01ff1f 0xfdfffff80fe00ff8

def z553 : W := mkw 0x9ffdffdf2026432a 0x24ffeffef9013219 0xbffffffe200e0707 0xf5fffffff1007038

def z554 : W := mkw 0x1580812bb036636a 0x20ac04095d81b31b 0xdf9187fffc7e67ff 0xfefc8c3fffe3f33f

def z555 : W := mkw 0x087028e042d0a8c1 0x8043814702168546 0x587000e1c3f000f9 0x72c380070e1f8007

def z556 : W := mkw 0x008081232034624a 0x200404091901a312 0x819187ff00706007 0xd40c8c3ff8038300

def z557 : W := mkw 0xbf7f7edc0d8b85b5 0x45fbfbf6e06c5c2d 0x7e6e7c983f8f87ff 0xbbf373e4c1fc7c3f

def z558 : W := mkw 0x020244000d090414 0x0010122000684820 0x666e64003f8f871f 0xbb33732001fc7c38

def z559 : W := mkw 0x0080012b20126362 0x200400095900931b 0x818007ff200067ec 0xdc0c003ff900033f

def z560 : W := mkw 0x0850000042400000 0x0042800002120000 0x18600000c3800010 0x20c30000061c0000

def z561 : W := mkw 0x0080810b2026432a 0x2004040859013219 0x4181879e200e07ef 0x9a0c0c3cf100703f

def z562 : W := mkw 0x5dfba8c1fb6c0018 0x02efdd460fdb6000 0xfffff8e1fffe001f 0xf7ffffc70ffff000

def z563 : W := mkw 0x1d7928e042d0a8c1 0x80ebc94702168546 0xfffff8e1c3f1f8ff 0xffffffc70e1f8fc7

def z564 : W := mkw 0x0000002a00122160 0x200000015000910b 0x000000fe000000e0 0x00000007f0000007

def z565 : W := mkw 0x2a746cf846d3ade5 0xc153a367c2369d6f 0xd8707cf9c3f1fffd 0x7ec383e7ce1f8fff

def z566 : W := mkw 0x087028c042c08881 0x8043814602160444 0x58707801c3f19819 0x72c383c00e1f8cc0

def z567 : W := mkw 0x40828001b92c0018 0x020414000dc96000 0x000000003c0e0000 0x0000000001e07000

def z568 : W := mkw 0x887d28d400000000 0x0443e946a0000000 0x206e000000000000 0x0103700000000000

def z569 : W := mkw 0x20060018090a0130 0x41003000c0485009 0x200e0018000e0002 0x01007000c0007000

def z570 : W := mkw 0x5dd98001f2640008 0x02eecc000f932000 0x3fff8001c0700003 0xf1fffc000e038000

def z571 : W := mkw 0x200200080d8b85b5 0x41001000406c5c2d 0x666e00003f8f87fb 0xbb33700001fc7c3f

def z572 : W := mkw 0x08d0896362746a4a 0xa046844b1b13a352 0x99919b67c0707800 0x44cc8cdb3e0383c0

def z573 : W := mkw 0x00800101b4015606 0x000400080da00ab0 0x000000003c000700 0x0000000001e00038

def z574 : W := mkw 0x22a665992d8bc7b7 0x4115332cc96c5e3d 0xe7ee67993f8fe7ff 0xff3f733cc9fc7f3f

def z575 : W := mkw 0x1700560004010404 0x00b802b000200820 0x9f807f003c01871c 0xfcfc03f801e00c38

def z576 : W := mkw 0x0000000000000000 0x0000000000000000 0x40000080000000ed 0x1a00000400000007

def z577 : W := mkw 0x9f7d7ffe00126362 0x24fbebfff000931b 0xbffffffe000067e7 0xfdfffffff000033f

def z578 : W := mkw 0x0080800920260128 0x0004040049013009 0x41918499207e07ef 0xda0c8c24c903f03f

def z579 : W := mkw 0x0000002000102040 0x0000000100008102 0x800000e0000060e4 0x0c00000700000307

def z580 : W := mkw 0x15800101b0004202 0x00ac00080d800210 0x9f800701fc00671c 0xfcfc00380fe00338

def z581 : W := mkw 0x9ffd7ff5f6d1fec7 0x84ffebffafb68ff6 0xfffffffffff1ffff 0xffffffffffff8fff

def z582 : W := mkw 0x1f59560000000000 0x00facab000000000 0xbfffff0000000007 0xf5fffff800000000

def z583 : W := mkw 0x5d7b28c0dbc88891 0x82ebd94606de4444 0x3e6e7800df819810 0x21f373c006fc0cc0

def z584 : W := mkw 0x17805701b4015606 0x00bc02b80da00ab0 0x99807f01c001ff04 0x4ccc03f80e000ff8

def z585 : W := mkw 0x80001a4400000000 0x040000d220000000 0x80001b6600000000 0x040000db30000000

def z586 : W := mkw 0x5fffe491fb6c0018 0x02ffff248fdb6000 0x7fffe499fffe001f 0xf3ffff24cffff000

def z587 : W := mkw 0x9ffdffff62f6ebeb 0xa4ffeffffb17b75f 0xffffffffe3ffffff 0xffffffffff1fffff

def z588 : W := mkw 0x0850084042400800 0x8042804202120040 0x18001800c0001800 0x00c000c0060000c0

def z589 : W := mkw 0x0200570004015606 0x001002b800200ab0 0x0000070000000700 0x0000003800000038

def z590 : W := mkw 0x000000200090a8c1 0x8000000100048546 0x000000000001f8e0 0x0800000000000fc7

def z591 : W := mkw 0x82247fd404015606 0x041123fea0200ab0 0x80007ffe0001ff04 0x0c0003fff0000ff8

def z592 : W := mkw 0x0850000042400000 0x0042800002120000 0x18100001c0700000 0x40c080000e038000

def z593 : W := mkw 0x002029ea0092ebe3 0xa001014f5004975f 0x80007ffe0001ffe4 0x0c0003fff0000fff

def z594 : W := mkw 0x887da8fe00362168 0x2443ed47f001b10b 0x607f80fe007e00e3 0x0303fc07f003f007

def z595 : W := mkw 0x0024209000000000 0x0001210480000000 0x206e009800000003 0x01037004c0000000

def z596 : W := mkw 0x200200000d898495 0x41001000006c4c24 0x000000001f818010 0x0000000000fc0c00

def z597 : W := mkw 0x1700560094011404 0x00b802b004a008a0 0x9e007801dc01f81c 0x7cf003c00ee00fc0

def z598 : W := mkw 0x0080800120240008 0x0004040009012000 0x40000001207e0008 0x020000000903f000

def z599 : W := mkw 0x1f7d649000000000 0x00fbeb2480000000 0x3fffe49800000007 0xf1ffff24c0000000

def z600 : W := mkw 0x1500000090000000 0x00a8000004800000 0x1e000000dc000010 0x20f0000006e00000

def z601 : W := mkw 0x8204561400000000 0x041022b0a0000000 0x0000071e00000000 0x00000038f0000000

def z602 : W := mkw 0x5dfba8c1fbec8899 0x82efdd460fdf6444 0x7ffff801ffff981b 0xf3ffffc00ffffcc0

def z603 : W := mkw 0x0080812b2036636a 0x200404095901b31b 0x819187ff007067e4 0x4c0c8c3ff803833f

def z604 : W := mkw 0x5dd9812bf276636a 0x22eecc095f93b31b 0xd99187ffe07e67ef 0xdecc8c3fff03f33f

def z605 : W := mkw 0x8a7d7ed400000000 0x0453ebf6a0000000 0xa07ffffe00000007 0x0503fffff0000000

def z606 : W := mkw 0x22246498048385a5 0x41112324c0241c2d 0x060064983c0187fc 0xb8300324c1e00c3f

def z607 : W := mkw 0x17805701b4015606 0x00bc02b80da00ab0 0x9f807f003c000704 0xf4fc03f801e00038

def z608 : W := mkw 0x222664980d0b0534 0x41113324c0685829 0x266e64983c0e0707 0xb1337324c1e07038

def z609 : W := mkw 0x9f7d7ed400000000 0x04fbebf6a0000000 0x3e7ff8fe00000003 0x21f3ffc7f0000000

def z610 : W := mkw 0x9d591a4400000000 0x04eac8d220000000 0x1800180000000000 0x00c000c000000000

def z611 : W := mkw 0x1d5b000009080010 0x00ead80000484000 0x7fff80003f8e001b 0xf3fffc0001fc7000

def z612 : W := mkw 0x0000000000000000 0x0000000000000000 0x000060000001801c 0x3800030000000c00

def z613 : W := mkw 0x0000002042d0a8c1 0x8000000102168546 0x4000000003f000e0 0x02000000001f8007

def z614 : W := mkw 0x222477980483d7a7 0x411123bcc0241ebd 0x80007f980001ffe4 0x0c0003fcc0000fff

def z615 : W := mkw 0x0000000800020120 0x0000000040001009 0x00000418200e0702 0x80000020c1007038

def z616 : W := mkw 0x0000012a00126362 0x200000095000931b 0xc01007ff007067ed 0x5e00803ff803833f

def z617 : W := mkw 0x48db80016b6c0018 0x0246dc000b5b6000 0x61ff800123fe000b 0xd30ffc00091ff000

def z618 : W := mkw 0x22a6e4992daf85bd 0x41153724c96d7c2d 0x67ffe4993fff87ff 0xfb3fff24c9fffc3f

def z619 : W := mkw 0x5fdbd601fb6c0018 0x02fedeb00fdb6000 0xffffff01fffe001f 0xf7fffff80ffff000

def z620 : W := mkw 0x17805701b4015606 0x00bc02b80da00ab0 0x1f807f00fc019f10 0xa0fc03f807e00cf8

def z621 : W := mkw 0x9f7d7ed400000000 0x04fbebf6a0000000 0xbe6e7ffe00000004 0x25f373fff0000000

def z622 : W := mkw 0x00a0a9eb20b6ebeb 0xa005054f5905b75f 0xc191ffff207fffef 0xde0c8ffff903ffff

def z623 : W := mkw 0x9f595e4400000000 0x04facaf220000000 0x9f91ff6600000004 0xf4fc8ffb30000000

def z624 : W := mkw 0x222677980d8bd7b7 0x411133bcc06c5ebd 0xe66e7f983f8fffff 0xbf3373fcc1fc7fff

def z625 : W := mkw 0x372676980d8b85b5 0x41b933b4c06c5c2d 0xffee7f983f8f87ff 0xffff73fcc1fc7c3f

def z626 : W := mkw 0x002020a042d0a8c1 0x8001010502168546 0x40606081c3f1f8fd 0x3a0303040e1f8fc7

def z627 : W := mkw 0x2a766cd84fcb8db5 0xc153b366c27e5c6d 0x7e6e7c98ff8f9fff 0xbbf373e4c7fc7cff

def z628 : W := mkw 0x800d001400000000 0x04006800a0000000 0x200f801e00000002 0x01007c00f0000000

def z629 : W := mkw 0x08f0a9eb2036636a 0x2047854f5901b31b 0xd9f1ffff207e67ef 0xfecf8ffff903f33f

def z630 : W := mkw 0x1d59000042400000 0x00eac80002120000 0x7fff8001c3f0001b 0xf3fffc000e1f8000

def z631 : W := mkw 0x002028e00090a8c1 0x8001014700048546 0x980078e1c001f8fc 0x7cc003c70e000fc7

def z632 : W := mkw 0x087028e00090a8c1 0x8043814700048546 0x987078e00001f8e5 0x7cc383c700000fc7

def z633 : W := mkw 0xdffffed5fb6c0018 0x06fffff6afdb6000 0x7ffff801fffe001b 0xf3ffffc00ffff000

def z634 : W := mkw 0x5ddb8861fb7c2858 0x82eedc430fdbe142 0xffff9861fffe781b 0xf7fffcc30ffff3c0

def z635 : W := mkw 0xbfff7fddbd8bd7b7 0x45fffbfeedec5ebd 0xffffffffff8fffff 0xfffffffffffc7fff

def z636 : W := mkw 0x0850002042502040 0x0042800102128102 0xd87000e1c3f060fd 0x7ec380070e1f8307

def z637 : W := mkw 0x20000008048385a5 0x4100000040241c2d 0x00000000000187e0 0x0800000000000c3f

def z638 : W := mkw 0x1dd00001f2400000 0x00ee80000f920000 0x5ff00001fff00019 0xf2ff80000fff8000

def z639 : W := mkw 0x17a07781b481d687 0x00bd03bc0da40eb4 0xdfe07f81ff81fffd 0xfeff03fc0ffc0fff

def z640 : W := mkw 0x687fa0984bee81b9 0x4343fd04c25f740d 0x607f809803fe00e3 0x0303fc04c01ff007

def z641 : W := mkw 0x5d590000d2400000 0x02eac80006920000 0x18000000c0000000 0x00c0000006000000

def z642 : W := mkw 0x220644180d0b0534 0x41103220c0685829 0x666e04183f8e071b 0xb3337020c1fc7038

def z643 : W := mkw 0x5ddb8001fb6c0018 0x02eedc000fdb6000 0x79ff8001c3fe0003 0x43cffc000e1ff000

def z644 : W := mkw 0x0859000000000000 0x0042c80000000000 0x207f800000000003 0x0103fc0000000000

def z645 : W := mkw 0x0002000009080010 0x0000100000484000 0x400000003f8e0018 0x0200000001fc7000

def z646 : W := mkw 0x5d5b0000db480010 0x02ead80006da4000 0x3fff8000df800013 0xf1fffc0006fc0000

def z647 : W := mkw 0x2a766cf84fdbadf5 0xc153b367c27edd6f 0x667e64f83fff87ff 0xbb33f327c1fffc3f

def z648 : W := mkw 0x0000802a00362168 0x200004015001b10b 0xc01180ff007e60ef 0x5e008c07f803f307

def z649 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000001c001f818 0x080000000e000fc0

def z650 : W := mkw 0x22266cf80d9badf5 0xc1113367c06cdd6f 0xe66e7cf83f8fffff 0xbf3373e7c1fc7fff

def z651 : W := mkw 0x087028e042d0a8c1 0x8043814702168546 0x407000e1c3f1f8f9 0x0a0380070e1f8fc7

def z652 : W := mkw 0x2082812b2dbfe7ff 0x61041409596dff3f 0xc19187ff3fffe7ff 0xde0c8c3ff9ffff3f

def z653 : W := mkw 0x3ff67ff9ffdbfff7 0xc1ffb3ffcffedfff 0xfffe7ff9ffffffff 0xfffff3ffcfffffff

def z654 : W := mkw 0x97a47fd5b4015606 0x04bd23feada00ab0 0x9f807ffffc01ff1c 0xfcfc03ffffe00ff8

def z655 : W := mkw 0x82247ed400000000 0x041123f6a0000000 0x8191fffe00000007 0xd40c8ffff0000000

def z656 : W := mkw 0x1fd05701f6415606 0x00fe82b80fb20ab0 0xdff07f01fff1ff1d 0xfeff83f80fff8ff8

def z657 : W := mkw 0x0850000042400000 0x0042800002120000 0xd8707801c3f1f81d 0x7ec383c00e1f8fc0

def z658 : W := mkw 0x1700560094011404 0x00b802b004a008a0 0x1e007c00fc019f1c 0xb8f003e007e00cf8

def z659 : W := mkw 0x0000000000000000 0x0000000000000000 0x0191800000000003 0xd00c8c0000000000

def z660 : W := mkw 0x0020208000808081 0x0001010400040404 0x40600080038000e1 0x02030004001c0007

def z661 : W := mkw 0xddd99a45f2640008 0x06eeccd22f932000 0x99919b67c0700000 0x44cc8cdb3e038000

def z662 : W := mkw 0x2a766cd04fc98c95 0xc153b366827e4c64 0x3e6e7800df819810 0x21f373c006fc0cc0

def z663 : W := mkw 0x1700560000000000 0x00b802b000000000 0x9f807f01c001f81c 0xfcfc03f80e000fc0

def z664 : W := mkw 0x55828001fb6c0018 0x02ac14000fdb6000 0x5f800001fffe0018 0xf2fc00000ffff000

def z665 : W := mkw 0x0850086042502840 0x8042804302128142 0xd81018e1c07078ed 0x5ec080c70e0383c7

def z666 : W := mkw 0x0000002042d0a8c1 0x8000000102168546 0xc01000e1c3f1f8fd 0x5e0080070e1f8fc7

def z667 : W := mkw 0x0850086042502840 0x8042804302128142 0x0010006000700000 0x0000800300038000

def z668 : W := mkw 0x17805701b4015606 0x00bc02b80da00ab0 0x9f801f01fc007f00 0xc4fc00f80fe003f8

def z669 : W := mkw 0xdf7ffed44b6c0018 0x06fbfff6a25b6000 0xfffffffe03fe0007 0xf7fffffff01ff000

def z670 : W := mkw 0x0080812bb437776e 0x200404095da1bbbb 0xc19187fffc7fffff 0xde0c8c3fffe3ffff

def z671 : W := mkw 0x0000010000004202 0x0000000800000210 0x8000070000006704 0x0c00003800000338

def z672 : W := mkw 0x5ddb8001fb6c0018 0x02eedc000fdb6000 0x3fff8001dff00010 0x61fffc000eff8000

def z673 : W := mkw 0x5dd98001f2640008 0x02eecc000f932000 0x59f18001c3f00019 0x72cf8c000e1f8000

def z674 : W := mkw 0x222664980d8b85b5 0x41113324c06c5c2d 0x260e64983c0f87e6 0x89307324c1e07c3f

def z675 : W := mkw 0x222664900d898495 0x41113324806c4c24 0x266e64981f818017 0xb1337324c0fc0c00

def z676 : W := mkw 0x0200440004010404 0x0010022000200820 0x060004003c000700 0x8030002001e00038

def z677 : W := mkw 0x17805721f6d1fec7 0x80bc02b90fb68ff6 0xdf807f01fff1fffc 0xfefc03f80fff8fff

def z678 : W := mkw 0x5f5b5600df491414 0x02fadab006fa48a0 0x3e6e7800df819810 0x21f373c006fc0cc0

def z679 : W := mkw 0x97247ed400000000 0x04b923f6a0000000 0x9f807ffe00000004 0xf4fc03fff0000000

def z680 : W := mkw 0x37825709bd8bd7b7 0x41bc12b84dec5ebd 0xdf807f01ff8ffffc 0xfefc03f80ffc7fff

def z681 : W := mkw 0x5dfba081fbec8099 0x02efdd040fdf6404 0x7fffe081ffff80ff 0xfbffff040ffffc07

def z682 : W := mkw 0x0080812b2036636a 0x200404095901b31b 0x41918001207e67eb 0xda0c8c000903f33f

def z683 : W := mkw 0x002020a00090a0c1 0x0001010500048506 0xc07060e103f1e0fd 0x7e038307081f8f07

def z684 : W := mkw 0x0000000000000000 0x0000000000000000 0x266e000000000003 0xb133700000000000

def z685 : W := mkw 0x40828001fb6c0018 0x020414000fdb6000 0x41918001fffe001b 0xd20c8c000ffff000

def z686 : W := mkw 0x0000000042400000 0x0000000002120000 0x40000001c3f00018 0x020000000e1f8000

def z687 : W := mkw 0x00800001b0000000 0x000400000d800000 0x00000001fc000018 0x000000000fe00000

def z688 : W := mkw 0x0850086042502840 0x8042804302128142 0xd8701861c3f07819 0x76c380c30e1f83c0

def z689 : W := mkw 0x1700570004015606 0x00b802b800200ab0 0x9f807f000001ff04 0xfcfc03f800000ff8

def z690 : W := mkw 0x485b802a4b7e2178 0x2242dc01525bf10b 0x607f80fe03fe00e3 0x0303fc07f01ff007

def z691 : W := mkw 0x0a706ce046d1acc5 0x8053836702368d66 0xde707ce1fff1fffd 0xfef383e70fff8fff

def z692 : W := mkw 0x5fd9d701f665560e 0x02feceb80fb32ab0 0x9f91ff01fc71ff1c 0xfcfc8ff80fe38ff8

def z693 : W := mkw 0x82a4ffff2036636a 0x241527fff901b31b 0xc191ffff207e67ef 0xde0c8ffff903f33f

def z694 : W := mkw 0x9f7d7ed400000000 0x04fbebf6a0000000 0x3ffff80000000003 0xf1ffffc000000000

def z695 : W := mkw 0x9ffd7fd5b4015606 0x04ffebfeada00ab0 0xbffffffe3c000707 0xf5fffffff1e00038

def z696 : W := mkw 0x0080800120240008 0x0004040009012000 0xc19187ff207e000f 0xd60c8c3ff903f000

def z697 : W := mkw 0x220644180d8b85b5 0x41103220c06c5c2d 0x660e04183f8f87fa 0x8b307020c1fc7c3f

def z698 : W := mkw 0x0850086042d0a8c1 0x8042804302168546 0xd8101861c3f1f8f8 0x4ec080c30e1f8fc7

def z699 : W := mkw 0x0000000000000000 0x0000000000000000 0x9800780000000004 0x74c003c000000000

def z700 : W := mkw 0x087028c042400000 0x0043814602120000 0xd87078e1c3f0001d 0x76c383c70e1f8000

def z701 : W := mkw 0x970d561400000000 0x04b86ab0a0000000 0x260e000000000000 0x0130700000000000

def z702 : W := mkw 0x0000000000000000 0x0000000000000000 0x0181871e00000002 0x800c0c38f0000000

def z703 : W := mkw 0x9f7d7ed400000000 0x04fbebf6a0000000 0xbfee7f0000000004 0xf5ff73f800000000

def z704 : W := mkw 0x7dffa099fbee81b9 0x43effd04cfdf740d 0x7fff8099fffe00fb 0xf3fffc04cffff007

def z705 : W := mkw 0x0224649004010404 0x0011232480200820 0x266e64983c01871f 0xb9337324c1e00c38

def z706 : W := mkw 0x17805701b0005202 0x00bc02b80d800290 0x9f807f01c0007804 0xf4fc03f80e0003c0

def z707 : W := mkw 0x0080812b2036636a 0x200404095901b31b 0xd99187ffe07e67ff 0xfecc8c3fff03f33f

def z708 : W := mkw 0x5ddb8101fb6c521a 0x02eedc080fdb6290 0x7fff8001fffe781b 0xf3fffc000ffff3c0

def z709 : W := mkw 0x9f7d7ed490001000 0x04fbebf6a4800080 0xbffffffec0001807 0xf5fffffff60000c0

def z710 : W := mkw 0x5ddb8001fb6c0018 0x02eedc000fdb6000 0x7fff8499fffe001f 0xf3fffc24cffff000

def z711 : W := mkw 0x972d7ed400000000 0x04b96bf6a0000000 0xa7effffe00000007 0xb53f7ffff0000000

def z712 : W := mkw 0x0859000000000000 0x0042c80000000000 0xa1ff87fe00000007 0xd50ffc3ff0000000

def z713 : W := mkw 0x5d5b8000db6c0018 0x02eadc0006db6000 0x7e6e0000dffe0010 0x23f3700006fff000

def z714 : W := mkw 0x9f5d5e5400000000 0x04faeaf2a0000000 0xbf9f9ffe00000007 0xd5fcfcfff0000000

def z715 : W := mkw 0x5789d701b425560e 0x02bc4eb80da12ab0 0x9f81ff01fc01ff1c 0xfcfc0ff80fe00ff8

def z716 : W := mkw 0x5ddb9201fb6c1018 0x02eedc900fdb6080 0x7fff9801fffe181b 0xf3fffcc00ffff0c0

def z717 : W := mkw 0x35a63399b98ad3b3 0x41ad319ccdcc569d 0xf9ee1b99c38e78e3 0x47cf70dcce1c73c7

def z718 : W := mkw 0x220244080d8b85b5 0x41101220406c5c2d 0x666e64003f8f87ff 0xbb33732001fc7c3f

def z719 : W := mkw 0x202620980d8b85b5 0x41013104c06c5c2d 0x666e00983f8f87fb 0xbb337004c1fc7c3f

def z720 : W := mkw 0x4a5bd7004f6d561e 0x0252deb8027b6ab0 0xe07fff0003ffff07 0x0f03fff8001ffff8

def z721 : W := mkw 0x9f5d5e5400000000 0x04faeaf2a0000000 0xbfff9f7e00000003 0xf5fffcfbf0000000

def z722 : W := mkw 0x002020a042d0a8c1 0x8001010502168546 0xd8607881c3f1f8fd 0x7ec303c40e1f8fc7

def z723 : W := mkw 0x970d563442d0a8c1 0x84b86ab1a2168546 0x678f871fc3f1f8fa 0x8b3c7c38fe1f8fc7

def z724 : W := mkw 0x88fd29d5b4015606 0x0447e94eada00ab0 0x207f80fffc01ff1b 0x0903fc07ffe00ff8

def z725 : W := mkw 0x0000000004010404 0x0000000000200820 0x98007801fc01ff1c 0x7cc003c00fe00ff8

def z726 : W := mkw 0x15800101b4015606 0x00ac00080da00ab0 0x9f807801fc01ff1c 0xfcfc03c00fe00ff8

def z727 : W := mkw 0x0080812bb036636a 0x200404095d81b31b 0xc19187fffc7e67ff 0xde0c8c3fffe3f33f

def z728 : W := mkw 0x222664980d8b85b5 0x41113324c06c5c2d 0x7e6e7c98ff8f9fff 0xbbf373e4c7fc7cff

def z729 : W := mkw 0x1724769000000000 0x00b923b480000000 0xbffffffe00000007 0xf5fffffff0000000

def z730 : W := mkw 0xdddb9a45fb6c0018 0x06eedcd22fdb6000 0xffff9ffffffe001f 0xf7fffcfffffff000

def z731 : W := mkw 0x222664980d8b85b5 0x41113324c06c5c2d 0x666e60003f8f87fb 0xbb33730001fc7c3f

def z732 : W := mkw 0x0080812b2036636a 0x200404095901b31b 0xd9919fffe07e7fef 0xdecc8cffff03f3ff

def z733 : W := mkw 0x9f7d7ed400000000 0x04fbebf6a0000000 0xbfffffff0000600f 0xfdfffffff8000300

def z734 : W := mkw 0x970d561400000000 0x04b86ab0a0000000 0xa79f877e00000002 0xc53cfc3bf0000000

def z735 : W := mkw 0x2082812b6fffefff 0xe10414095b7fff7f 0x40000001fffffff8 0x0a0000000fffffff

def z736 : W := mkw 0x5ddb8001fb6c0018 0x02eedc000fdb6000 0xffff8701fffe001f 0xf7fffc380ffff000

def z737 : W := mkw 0x40828001fb6c0018 0x020414000fdb6000 0x67ff8001fffe001b 0xf33ffc000ffff000

def z738 : W := mkw 0xc2a6fed5fb6c0018 0x061537f6afdb6000 0xc0007ffffffe001c 0x060003fffffff000

def z739 : W := mkw 0x9f7d7ed400000000 0x04fbebf6a0000000 0xb9fffffe00000007 0x45cffffff0000000

def z740 : W := mkw 0x0000002042d0a8c1 0x8000000102168546 0x58007801c3f1f8f8 0x2ac003c00e1f8fc7

def z741 : W := mkw 0x22247ff80493ffe7 0xc11123ffc0249fff 0x80007ff80001ffe4 0x0c0003ffc0000fff

def z742 : W := mkw 0x1780d701b425560e 0x00bc06b80da12ab0 0x9f81ff01fc0fff1e 0xfcfc0ff80fe07ff8

def z743 : W := mkw 0x887d28f442d0a8c1 0x8443e947a2168546 0xf87e78e1c3f1f8fd 0x7fc3f3c70e1f8fc7

def z744 : W := mkw 0x9f7d7ed442c08881 0x84fbebf6a2160444 0xfffffffec38198ff 0xfffffffff61c0cc7

def z745 : W := mkw 0x1700570094015606 0x00b802b804a00ab0 0x1e007800dc01ff10 0x28f003c006e00ff8

def z746 : W := mkw 0x222664980d8b85b5 0x41113324c06c5c2d 0x666e64003f8f87fc 0xbb33732001fc7c3f

def z747 : W := mkw 0x887d28f442d0a8c1 0x8443e947a2168546 0xf9ffffffc3f1f8ff 0xffcffffffe1f8fc7

def z748 : W := mkw 0x558b8001fb6c0018 0x02ac5c000fdb6000 0x67ef8001fffe001b 0xb33f7c000ffff000

def z749 : W := mkw 0x0080812b2036636a 0x200404095901b31b 0x419187fe207e07ef 0x9a0c8c3ff103f03f

def z750 : W := mkw 0x55aba8e1b9bca8d9 0x82ad5d470dcde546 0xa78ff8e03c0ff8e6 0x8d3c7fc701e07fc7

def z751 : W := mkw 0x9f7d7ed400808081 0x04fbebf6a0040404 0xfffffffe038000e7 0xf7fffffff01c0007

def z752 : W := mkw 0x40828001fb6c0018 0x020414000fdb6000 0x666e0001fffe0018 0x233370000ffff000

def z753 : W := mkw 0x222664980d8b85b5 0x41113324c06c5c2d 0x666e04983f8e07fb 0xb3337024c1fc703f

def z754 : W := mkw 0x1d5b00004b480010 0x00ead800025a4000 0x7fff8001fffe001b 0xf3fffc000ffff000

def z755 : W := mkw 0x887d28d400000000 0x0443e946a0000000 0xa1ff83fe00000003 0x450ffc1ff0000000

def z756 : W := mkw 0x0a746cd000000000 0x0053a36680000000 0xbffffffe00000007 0xf5fffffff0000000

def z757 : W := mkw 0x970d561400000000 0x04b86ab0a0000000 0x279f87fe00000003 0x813cfc3ff0000000

def z758 : W := mkw 0x20262098098a81b1 0x41013104c04c540d 0x666e04983f8e07ff 0xbb337024c1fc703f

def z759 : W := mkw 0x17805701b4015606 0x00bc02b80da00ab0 0x9f807b01fc01ff18 0x6cfc03d80fe00ff8

def z760 : W := mkw 0x5d5b012adb5a6372 0x22ead80956dad31b 0xbe6e07fedf8067f4 0x2df3703ff6fc033f

def z761 : W := mkw 0x9f7d7ed442400000 0x04fbebf6a2120000 0xbffffffec3800017 0xf5fffffff61c0000

def z762 : W := mkw 0xa226769c0d8b85b5 0x451133b4e06c5c2d 0x666e679e3f8f87ff 0xbb33733cf1fc7c3f

def z763 : W := mkw 0x5ddb8101fb6c421a 0x02eedc080fdb6210 0xffff87fffffe671f 0xfffffc3ffffff338

def z764 : W := mkw 0x970d5e5400000000 0x04b86af2a0000000 0xa78f9f7e00000002 0x853c7cfbf0000000

def z765 : W := mkw 0x978d5715b4015606 0x04bc6ab8ada00ab0 0xbf9ffffffc01ff1f 0xfdfcffffffe00ff8

def z766 : W := mkw 0x1700d62a9437356c 0x20b806b154a1b9ab 0x5e11f8fedc7f98f3 0x22f08fc7f6e3fcc7

def z767 : W := mkw 0x0080800920260128 0x0004040049013009 0xc19187ff207e07ef 0xde0c8c3ff903f03f

def z768 : W := mkw 0x087428f042d0a8c1 0x8043a14782168546 0xf87e78f9c3f1f8ff 0x7fc3f3c7ce1f8fc7

def z769 : W := mkw 0x1700570094015606 0x00b802b804a00ab0 0x9e007f00fc01ff1c 0xbcf003f807e00ff8

def z770 : W := mkw 0x558b8001b92c0018 0x02ac5c000dc96000 0x67ff80013ffe001b 0xf33ffc0009fff000

def z771 : W := mkw 0x0080812b2036636a 0x200404095901b31b 0xc19187ff207e67e3 0xc60c8c3ff903f33f

def z772 : W := mkw 0x222664980d8b85b5 0x41113324c06c5c2d 0xe66e7c983f8fffff 0xbf3373e4c1fc7fff

def z773 : W := mkw 0x222664980d8b85b5 0x41113324c06c5c2d 0x667fe4fe3f8f87ff 0xbb33ff27f1fc7c3f

def z774 : W := mkw 0x087028e042d0a8c1 0x8043814702168546 0x587078e1c3f1f8f9 0x2ac383c70e1f8fc7

def z775 : W := mkw 0x800d001400000000 0x04006800a0000000 0xa19f87fe00000007 0xd50cfc3ff0000000

def z776 : W := mkw 0x22246cf80493ade5 0xc1112367c0249d6f 0x000064f8000187e4 0x08000327c0000c3f

def z777 : W := mkw 0x9ffdffff2036636a 0x24ffeffff901b31b 0x7e6e7801207e67e8 0x2bf373c00903f33f

def z778 : W := mkw 0x17805701b4015606 0x00bc02b80da00ab0 0x9e007f01fc01ff1c 0x2cf003f80fe00ff8

def z779 : W := mkw 0x202220880d8b85b5 0x41011104406c5c2d 0x666e60803f8f87ff 0xbb33730401fc7c3f

def z780 : W := mkw 0x9f5d561400000000 0x04faeab0a0000000 0xbfff87fe00000007 0xf5fffc3ff0000000

def z781 : W := mkw 0x0850002042502040 0x0042800102128102 0xd87078e1c3f1f8fd 0x7ec383c70e1f8fc7

def z782 : W := mkw 0x087028e042d0a8c1 0x8043814702168546 0xd8707cf9c3f1f8ff 0xfec383e7ce1f8fc7

def z783 : W := mkw 0x2a564c784f5b2d74 0xc152b263c27ad96b 0xbe1e1c79fc7e7f02 0xc5f0f0e3cfe3f3f8

def z784 : W := mkw 0xbd5b1a4c0d8b85b5 0x45ead8d2606c5c2d 0xd9919b663f8f87f8 0x4ecc8cdb31fc7c3f

def z785 : W := mkw 0x970d561400000000 0x04b86ab0a0000000 0xbf9ffffe00000007 0xf5fcfffff0000000

def z786 : W := mkw 0x5ddb8101fb6c421a 0x02eedc080fdb6210 0x7fff8701fffe071b 0xf3fffc380ffff038

def z787 : W := mkw 0x400280004b6c0018 0x02001400025b6000 0x666e00003ffe001b 0xb333700001fff000

def z788 : W := mkw 0x222464ba0493a5e5 0x61112325d0249d2f 0x000064fe000187e4 0x08000327f0000c3f

def z789 : W := mkw 0xa2267edc0d8b85b5 0x451133f6e06c5c2d 0xe7fffffe3f8f87ff 0xff3ffffff1fc7c3f

def z790 : W := mkw 0x9f7d7ed400000000 0x04fbebf6a0000000 0xbffffffe3c00001f 0xf5fffffff1e00000

def z791 : W := mkw 0x9f7d7ed400000000 0x04fbebf6a0000000 0xffffffff0070000f 0xf7fffffff8038000

def z792 : W := mkw 0x17805701b4015606 0x00bc02b80da00ab0 0x9f907fe1fc01ff1d 0xfcfc83ff0fe00ff8

def z793 : W := mkw 0x0000002800122160 0x000000014000910b 0xc19187ff207e67ef 0xde0c8c3ff903f33f

def z794 : W := mkw 0x0080812b2036636a 0x200404095901b31b 0xc191ffff207fffef 0xde0c8ffff903ffff

def z795 : W := mkw 0x00800101b4015606 0x000400080da00ab0 0x18007801fc01ff18 0x28c003c00fe00ff8

def z796 : W := mkw 0xa87f28fc4bdaa9f1 0xc543f947e25ed54f 0x607f80fe03fe00e3 0x0303fc07f01ff007

def z797 : W := mkw 0x9f7d7ed400000000 0x04fbebf6a0000000 0xbffffffec0019817 0xf5fffffff6000cc0

def z798 : W := mkw 0xa2267edc0d8b85b5 0x451133f6e06c5c2d 0x666e7c983f8f87ff 0xbb3373e4c1fc7c3f

def z799 : W := mkw 0x9d7d3ad400000000 0x04ebe9d6a0000000 0xb9fffbfe00000007 0x75cfffdff0000000

def z800 : W := mkw 0x5ddb8001fb6c0018 0x02eedc000fdb6000 0x67ff80013ffe000b 0xd33ffc0009fff000

def z801 : W := mkw 0x1ff07fe1f6d1fec7 0x80ff83ff0fb68ff6 0x47f007e03ff007e1 0x823f803f01ff803f

def z802 : W := mkw 0xff7f7ed4dfc98495 0x47fbfbf6a6fe4c24 0x3e6e7800df818010 0x21f373c006fc0c00

def z803 : W := mkw 0x9f7d7ed400000000 0x04fbebf6a0000000 0xbfffff7e00000002 0xe5fffffbf0000000

def z804 : W := mkw 0x222664980d8b85b5 0x41113324c06c5c2d 0xe67e64f83f8f87ff 0xff33f327c1fc7c3f

def z805 : W := mkw 0x1dd20001fb480010 0x00ee90000fda4000 0x7ffe0001fffe001b 0xf3fff0000ffff000

def z806 : W := mkw 0x887428f442d0a8c1 0x8443a147a2168546 0xd87078ffc3f1f8fd 0x7ec383c7fe1f8fc7

def z807 : W := mkw 0x5ddb9301fb6c521a 0x02eedc980fdb6290 0x7fff8301fffe001b 0xf3fffc180ffff000

def z808 : W := mkw 0x02805701b4015606 0x001402b80da00ab0 0x98007f01fc01ff1c 0x7cc003f80fe00ff8

def z809 : W := mkw 0x5ddb8001fb6c0018 0x02eedc000fdb6000 0x67ff80003ffe001b 0xb33ffc0001fff000

def z810 : W := mkw 0x9f7d7ed400000000 0x04fbebf6a0000000 0x27ffe7fe00000007 0xb13fff3ff0000000

def z811 : W := mkw 0xbf7f7ed44fc98c95 0xc5fbfbf6a27e4c64 0x3e6e7800df819810 0x21f373c006fc0cc0

def z812 : W := mkw 0x0024209000000000 0x0001210480000000 0xa1ff87fe00000007 0xd50ffc3ff0000000

def z813 : W := mkw 0x887d28d400000000 0x0443e946a0000000 0x21ff87fe00000003 0x810ffc3ff0000000

def z814 : W := mkw 0x15828001b92c0018 0x00ac14000dc96000 0x7fff8001fffe001b 0xf3fffc000ffff000

def z815 : W := mkw 0x02266498090a0130 0x00113324c0485009 0x666e64983f8e07ff 0xbb337324c1fc703f

def z816 : W := mkw 0x222664980d8b85b5 0x41113324c06c5c2d 0x666e6499ff8fffff 0xbb337324cffc7fff

def z817 : W := mkw 0x485b80004b6c0018 0x0242dc00025b6000 0x667f80001ffe0013 0x2333fc0000fff000

def z818 : W := mkw 0xbf7d7ed404818485 0x45fbebf6a0240c24 0xbffffffe00018007 0xf5fffffff0000c00

def z819 : W := mkw 0x5ddb8001fb6c0018 0x02eedc000fdb6000 0x7fff80003ffe0003 0xf3fffc0001fff000

def z820 : W := mkw 0x0080812b2036636a 0x200404095901b31b 0xc79187ff3c7e67ff 0xfe3c8c3ff9e3f33f

def z821 : W := mkw 0x978d5715b4015606 0x04bc6ab8ada00ab0 0xbf8e7f01fc01ff1c 0xfdfc73f80fe00ff8

def z822 : W := mkw 0x9d7d3ad400000000 0x04ebe9d6a0000000 0xb9ff9ffe00000007 0xd5cffcfff0000000

def z823 : W := mkw 0x087028e042d0a8c1 0x8043814702168546 0xd8707fffc3f1f8fd 0x7ec383fffe1f8fc7

def z824 : W := mkw 0x485b80004b6c0018 0x0242dc00025b6000 0x667f80003ffe0003 0x8333fc0001fff000

def z825 : W := mkw 0x9f7d7ed400808081 0x04fbebf6a0040404 0xffffffffc381f8ff 0xfffffffffe1c0fc7

def z826 : W := mkw 0x9f7d7ed442c08881 0x84fbebf6a2160444 0xbffffffe03800007 0xf5fffffff01c0000

def z827 : W := mkw 0x087028e042d0a8c1 0x8043814702168546 0xd9f1f8e1c3f1f8ff 0xfecf8fc70e1f8fc7

def z828 : W := mkw 0x970d561400000000 0x04b86ab0a0000000 0xa78f87fe00000006 0x853c7c3ff0000000

def z829 : W := mkw 0x9f7d7ed400000000 0x04fbebf6a0000000 0x3ffffffe00000003 0xa1fffffff0000000

def z830 : W := mkw 0x687fa8f84bfea9f9 0xc343fd47c25ff54f 0x607f80f803fe00e3 0x0303fc07c01ff007

def z831 : W := mkw 0x9f7d7ed490000000 0x04fbebf6a4800000 0xbffffffedc000017 0xf5fffffff6e00000

def z832 : W := mkw 0x17805701b4015606 0x00bc02b80da00ab0 0x9f807f99fc01ff1f 0xfcfc03fccfe00ff8

def z833 : W := mkw 0x9f7d7ed400000000 0x04fbebf6a0000000 0x3fff87fe00000003 0xf1fffc3ff0000000

def z834 : W := mkw 0x0080812b2036636a 0x200404095901b31b 0xc19187fe207e07e7 0xd60c8c3ff103f03f

def z835 : W := mkw 0x7ffde499f6e785ad 0x43ffef24cfb73c2d 0x1991e499c07187e4 0x48cc8f24ce038c3f

def z836 : W := mkw 0x17805701b4015606 0x00bc02b80da00ab0 0xdf807f81fc01fffd 0xfefc03fc0fe00fff

def z837 : W := mkw 0x22a6e5b32dbde6df 0x6115372d996def36 0xa7ffe3671ff1e010 0x653fff1b38ff8f00

def z838 : W := mkw 0x1700570094015606 0x00b802b804a00ab0 0x9f807f00dc01ff14 0xfcfc03f806e00ff8

def z839 : W := mkw 0x087028e042d0a8c1 0x8043814702168546 0x58607881c3f1f8fd 0x3ac303c40e1f8fc7

def z840 : W := mkw 0x5dd99b61f2747a4a 0x82eeccdb0f93a3d2 0x99919b61c0707800 0x44cc8cdb0e0383c0

def z841 : W := mkw 0x9f7d7ed404010404 0x04fbebf6a0200820 0xbffffffe00018707 0xfdfffffff0000c38

def z842 : W := mkw 0x887928e442d0a8c1 0x8443c94722168546 0xd871f8e7c3f1f8fd 0x7ec38fc73e1f8fc7

def z843 : W := mkw 0xdf7d7ed4d2400000 0x06fbebf6a6920000 0xbffffffec0000007 0xf5fffffff6000000

def z844 : W := mkw 0x9f7d7ed400000000 0x04fbebf6a0000000 0xbfffffffc0007807 0xf5fffffffe0003c0

def z845 : W := mkw 0x17805701b4015606 0x00bc02b80da00ab0 0x1f807f01fc01ff18 0xa8fc03f80fe00ff8

def z846 : W := mkw 0x222664980d8b85b5 0x41113324c06c5c2d 0x666e60983f8f87fb 0x2b337304c1fc7c3f

def z847 : W := mkw 0x22246dfa0493efe7 0xe111236fd0249f7f 0x80007ffe0001ffe4 0x0c0003fff0000fff

def z848 : W := mkw 0x48db80016b6c0018 0x0246dc000b5b6000 0x67ff80013ffe001b 0xf33ffc0009fff000

def z849 : W := mkw 0x5ddb8001fb6c0018 0x02eedc000fdb6000 0x7e7f8001fffe001b 0x23f3fc000ffff000

def z850 : W := mkw 0x087028e042d0a8c1 0x8043814702168546 0xd871f8ffc3f1f8ff 0x7ec38fc7fe1f8fc7

def z851 : W := mkw 0x9f7d7ed400000000 0x04fbebf6a0000000 0xfffffffe200e000f 0xf7fffffff1007000

def z852 : W := mkw 0x08f0a9cb62e6cbab 0xa047854e5b17365d 0x19e1ff1ee38f9f12 0xa0cf0ff8f71c7cf8

def z853 : W := mkw 0x9d7d28d400000000 0x04ebe946a0000000 0xbfff87fe00000007 0xf5fffc3ff0000000

def z854 : W := mkw 0xa2247ffe0493e7e7 0x651123fff0249f3f 0x80007ffe0001e7e4 0x0c0003fff0000f3f

def z855 : W := mkw 0x222664980d8b85b5 0x41113324c06c5c2d 0xfe6e7c983f8f87ff 0xfff373e4c1fc7c3f

def z856 : W := mkw 0x17805701b4015606 0x00bc02b80da00ab0 0x9f807f01dc01ff14 0x6cfc03f80ee00ff8

def z857 : W := mkw 0xdddb9205fb6c0018 0x06eedc902fdb6000 0x7fff8307fffe001b 0xf3fffc183ffff000

def z858 : W := mkw 0x5dd99323f274724a 0x22eecc991f93a392 0x99919b67c0707800 0x44cc8cdb3e0383c0

def z859 : W := mkw 0x00028000092c0018 0x0000140000496000 0x667f80003ffe001b 0xb333fc0001fff000

def z860 : W := mkw 0x5ddb8841fb6c0018 0x02eedc420fdb6000 0xffff9861fffe001b 0xf7fffcc30ffff000

def z861 : W := mkw 0x1780d703b425560e 0x20bc06b81da12ab0 0x9f81ff07fc01ff1c 0xfcfc0ff83fe00ff8

def z862 : W := mkw 0x00828001292c0018 0x0004140009496000 0x666e00013ffe001b 0xb333700009fff000

def z863 : W := mkw 0x9d5d1a5400000000 0x04eae8d2a0000000 0xb99f9b7e00000002 0x45ccfcdbf0000000

def z864 : W := mkw 0x085200004b480010 0x00429000025a4000 0x667e00003ffe001b 0xb333f00001fff000

def z865 : W := mkw 0x17895701b4015606 0x00bc4ab80da00ab0 0xbf8fff01fc01ff1e 0xfdfc7ff80fe00ff8

def z866 : W := mkw 0x5d5b80004b6c0018 0x02eadc00025b6000 0x7fff80003ffe001b 0xf3fffc0001fff000

def z867 : W := mkw 0xddd99b67f274624a 0x26eeccdb3f93a312 0x99919b67c0706000 0x44cc8cdb3e038300

def z868 : W := mkw 0x9f7d7ed442400800 0x84fbebf6a2120040 0xbffffffec0001807 0xf5fffffff60000c0

def z869 : W := mkw 0xa2247efc0493ade5 0xc51123f7e0249d6f 0x80007ffe0001ffe4 0x0c0003fff0000fff

def z870 : W := mkw 0x0204441000000000 0x0010222080000000 0xa79f87fe00000007 0xd53cfc3ff0000000

def z871 : W := mkw 0x020244080d0b0534 0x0010122040685829 0x666e64983f8f87ff 0xbb337324c1fc7c3f

def z872 : W := mkw 0x9f7d7ed400000000 0x04fbebf6a0000000 0xbffffffe0001f807 0xfdfffffff0000fc0

def z873 : W := mkw 0x17805701b4015606 0x00bc02b80da00ab0 0xbfee7f01fc01ff1f 0xfdff73f80fe00ff8

def z874 : W := mkw 0x5ddb8001fb6c0018 0x02eedc000fdb6000 0xffff8001fffe601f 0xfffffc000ffff300

def z875 : W := mkw 0x222464b80493a5e5 0x41112325c0249d2f 0x800064f80001e7e4 0x0c000327c0000f3f

def z876 : W := mkw 0x9f7d7ed400000000 0x04fbebf6a0000000 0xbffffbfe00000003 0x65ffffdff0000000

def z877 : W := mkw 0x9f7d7ed400808081 0x04fbebf6a0040404 0xbffffffe03818017 0xf5fffffff01c0c00

def z878 : W := mkw 0x0080812b2036636a 0x200404095901b31b 0xc191e7ff207fe7ff 0xfe0c8f3ff903ff3f

def z879 : W := mkw 0x08d280016b6c0018 0x004694000b5b6000 0x7fff8001fffe001b 0xf3fffc000ffff000

def z880 : W := mkw 0x17805701b4015606 0x00bc02b80da00ab0 0x9f91ff01fc01ff1f 0xfcfc8ff80fe00ff8

def z881 : W := mkw 0x972d7ed400000000 0x04b96bf6a0000000 0x278f87fe00000002 0x813c7c3ff0000000

def z882 : W := mkw 0xa2266cdc0d8b85b5 0x45113366e06c5c2d 0x666e64fe3f8f87ff 0xbb337327f1fc7c3f

def z883 : W := mkw 0x9f7d7ed494011404 0x04fbebf6a4a008a0 0xbffffffefc019f1f 0xfdfffffff7e00cf8

def z884 : W := mkw 0x5d5b8000db6c0018 0x02eadc0006db6000 0x667f80001ffe0003 0x0333fc0000fff000

def z885 : W := mkw 0x9f7d7ed400808081 0x04fbebf6a0040404 0xbffffffe000180e7 0xfdfffffff0000c07

def z886 : W := mkw 0x0080812b2036636a 0x200404095901b31b 0x419187ff207e07eb 0xd20c8c3ff903f03f

def z887 : W := mkw 0x9f7d7ed400000000 0x04fbebf6a0000000 0xa7ff87fe00000007 0xd53ffc3ff0000000

def z888 : W := mkw 0x82247ed400000000 0x041123f6a0000000 0xa7fffffe00000007 0xf53ffffff0000000

def z889 : W := mkw 0x9f7d7ed442400000 0x04fbebf6a2120000 0xfffffffe03f00007 0xf7fffffff01f8000

def z890 : W := mkw 0x087028e042d0a8c1 0x8043814702168546 0xfe7e78e1c3f1f8ff 0xfff3f3c70e1f8fc7

def z891 : W := mkw 0x9f7d7ed404011404 0x04fbebf6a02008a0 0xbffffffe00019807 0xf5fffffff0000cc0

def z892 : W := mkw 0xdddb9a45fb6c0018 0x06eedcd22fdb6000 0x7fff9801fffe001b 0xf3fffcc00ffff000

def z893 : W := mkw 0x55828001fb6c0018 0x02ac14000fdb6000 0x7fee0001fffe001b 0xf3ff70000ffff000

def z894 : W := mkw 0x972d7ed400000000 0x04b96bf6a0000000 0xa79ffffe00000007 0xd53cfffff0000000

def z895 : W := mkw 0x220644180d0b0534 0x41103220c0685829 0x666e04983f8e07ff 0xbb337024c1fc703f

def z896 : W := mkw 0x222664980d8b85b5 0x41113324c06c5c2d 0x666e64983f8e07e7 0xb3337324c1fc703f

def z897 : W := mkw 0x222664980d8b85b5 0x41113324c06c5c2d 0x666e64983f8f87f3 0xa3337324c1fc7c3f

def z898 : W := mkw 0x15800101b0004202 0x00ac00080d800210 0x9f807f01fc01ff1c 0xfcfc03f80fe00ff8

def z899 : W := mkw 0x2082812bbdbff7ff 0x610414095dedffbf 0x40000001fffffff8 0x0a0000000fffffff

def z900 : W := mkw 0x48db8001fb6c0018 0x0246dc000fdb6000 0x667f8001fffe001b 0xb333fc000ffff000

def z901 : W := mkw 0x9f7d7ed494011404 0x04fbebf6a4a008a0 0xbfffffffdc01f81f 0xfdfffffffee00fc0

def z902 : W := mkw 0x222664980d8b85b5 0x41113324c06c5c2d 0x7e6e6499ff8f87ff 0xfbf37324cffc7c3f

def z903 : W := mkw 0x97845715b4015606 0x04bc22b8ada00ab0 0x9f807f1ffc01ff1c 0xfcfc03f8ffe00ff8

def z904 : W := mkw 0x0870208042c08081 0x0043810402160404 0xd8707881c3f1f8fd 0x7ec383c40e1f8fc7

def z905 : W := mkw 0x9f7d7ed400000000 0x04fbebf6a0000000 0xbfff9ffe00000003 0xc5fffcfff0000000

def z906 : W := mkw 0x9f7d7ed400000000 0x04fbebf6a0000000 0xbf9ffffe00000006 0xc5fcfffff0000000

def z907 : W := mkw 0x5ddb8101fb6c421a 0x02eedc080fdb6210 0xffffff01ffffff1f 0xfffffff80ffffff8

def z908 : W := mkw 0x087028e042d0a8c1 0x8043814702168546 0xd86078e1c3f1f8fc 0x2ec303c70e1f8fc7

def z909 : W := mkw 0x972d7ed400000000 0x04b96bf6a0000000 0xbf8ffffe00000006 0xf5fc7ffff0000000

def z910 : W := mkw 0x087028e042d0a8c1 0x8043814702168546 0xd87078e1c3f1f8f1 0x66c383c70e1f8fc7

def z911 : W := mkw 0x5d5b8000db6c0018 0x02eadc0006db6000 0x7e7f8000fffe001b 0xb3f3fc0007fff000

def z912 : W := mkw 0x9f7d7ed442c08881 0x84fbebf6a2160444 0xbfffffffc381f81f 0xfdfffffffe1c0fc0

def z913 : W := mkw 0x5ddb8001fb6c0018 0x02eedc000fdb6000 0xffff9801fffe781b 0xf7fffcc00ffff3c0

def z914 : W := mkw 0x5ddb8001fb6c0018 0x02eedc000fdb6000 0x7e7e0001fffe0019 0x73f3f0000ffff000

def z915 : W := mkw 0x222664980d8b85b5 0x41113324c06c5c2d 0x67ffe4983f8f87ff 0xfb3fff24c1fc7c3f

def z916 : W := mkw 0x022264800d898495 0x00111324006c4c24 0x666e64803f8f87ff 0xbb33732401fc7c3f

def z917 : W := mkw 0x0000000000000000 0x0000000000000000 0xa7ff87fe00000007 0xf53ffc3ff0000000

def z918 : W := mkw 0x00800101b4015606 0x000400080da00ab0 0x99807f01fc01ff1c 0xfccc03f80fe00ff8

def z919 : W := mkw 0x0002000009080010 0x0000100000484000 0x667e00013ffe001b 0xf333f00009fff000

def z920 : W := mkw 0x17805701b4015606 0x00bc02b80da00ab0 0x9e007801fc01ff1c 0x7cf003c00fe00ff8

def z921 : W := mkw 0x087028e042d0a8c1 0x8043814702168546 0xd9f07fe1c3f1f8fd 0xfecf83ff0e1f8fc7

def z922 : W := mkw 0x5ddb9301fb6c521a 0x02eedc980fdb6290 0xffff9f01fffe7f1f 0xfffffcf80ffff3f8

def z923 : W := mkw 0x578bd70bbd2f573e 0x22bc5eb85de97ab9 0x278f871e3c0e0702 0x813c7c38f1e07038

def z924 : W := mkw 0x5ddb8001fb6c0018 0x02eedc000fdb6000 0x7fff8081fffe00ff 0xfbfffc040ffff007

def z925 : W := mkw 0x222664980d8b85b5 0x41113324c06c5c2d 0x666e04983f8e07ef 0x9b337024c1fc703f

def z926 : W := mkw 0x3786d71bbd2f573e 0x61bc36b8dde97ab9 0x278f871e3c0e0702 0x813c7c38f1e07038

def z927 : W := mkw 0x222664980d8b85b5 0x41113324c06c5c2d 0x666e04983f8f87fb 0x8b337024c1fc7c3f

def z928 : W := mkw 0x17805701b4015606 0x00bc02b80da00ab0 0x9f807f00fc01ff14 0xacfc03f807e00ff8

def z929 : W := mkw 0x9f7d7ed494011404 0x04fbebf6a4a008a0 0xbffffffe1c000007 0xf5fffffff0e00000

def z930 : W := mkw 0x5ddb8101fb6c421a 0x02eedc080fdb6210 0x7fff8001fffe671b 0xfbfffc000ffff338

def z931 : W := mkw 0x5ddb8001fb6c0018 0x02eedc000fdb6000 0x7fff8001fffe0018 0x63fffc000ffff000

def z932 : W := mkw 0x00020008090a0130 0x0000100040485009 0x666e00003f8e07fb 0xbb33700001fc703f

def z933 : W := mkw 0x5ddb8001fb6c0018 0x02eedc000fdb6000 0x67ff8001fffe001b 0x833ffc000ffff000

def z934 : W := mkw 0x5ddb8001fb6c0018 0x02eedc000fdb6000 0x7fff8001fffe0003 0xc3fffc000ffff000

def z935 : W := mkw 0x0080812b2036636a 0x200404095901b31b 0xc19187fe207e67e7 0x8e0c8c3ff103f33f

def z936 : W := mkw 0x0080812b2036636a 0x200404095901b31b 0xd991ffff207e67ef 0xfecc8ffff903f33f

def z937 : W := mkw 0x5ddb9301fb6c521a 0x02eedc980fdb6290 0xfffffb01fffff81f 0xffffffd80fffffc0

def z938 : W := mkw 0x0280450124014606 0x0014022809200a30 0x9f807f01fc01ff1c 0xfcfc03f80fe00ff8

def z939 : W := mkw 0x487ba8ea4bfea9f9 0xa243dd47525ff54f 0x607f80fe03fe00e3 0x0303fc07f01ff007

def z940 : W := mkw 0x200200080d8b85b5 0x41001000406c5c2d 0x666e00003f8f87f8 0x2b33700001fc7c3f

def z941 : W := mkw 0x9f7d7ed404818485 0x04fbebf6a0240c24 0xfffffffe3f8187ff 0xfffffffff1fc0c3f

def z942 : W := mkw 0x17805701b4015606 0x00bc02b80da00ab0 0xdf807f01fc0fff1f 0xfefc03f80fe07ff8

def z943 : W := mkw 0x4082812bfbfeebfb 0xa20414095fdff75f 0x40000001fffffff8 0x0a0000000fffffff

def z944 : W := mkw 0x485b80004b6c0018 0x0242dc00025b6000 0x7e7f8001fffe001b 0xf3f3fc000ffff000

def z945 : W := mkw 0x087028e042d0a8c1 0x8043814702168546 0x58707801c3f1f8f9 0x7ac383c00e1f8fc7

def z946 : W := mkw 0x222664980d8b85b5 0x41113324c06c5c2d 0x667e64993fff87ff 0xfb33f324c9fffc3f

def z947 : W := mkw 0x2082812b2d3f677e 0x610414095969fb3b 0x400000013c7e67e8 0x0a00000009e3f33f

def z948 : W := mkw 0x0000802a00362168 0x200004015001b10b 0xc19187fe207e07ef 0xde0c8c3ff103f03f

def z949 : W := mkw 0x1f59560000000000 0x00facab000000000 0xbffffffe00000007 0xf5fffffff0000000

def z950 : W := mkw 0x1780d701b425560e 0x00bc06b80da12ab0 0xdf91fffffc7fff1f 0xfefc8fffffe3fff8

def z951 : W := mkw 0x9f7d7ed404010404 0x04fbebf6a0200820 0xbffffffe3c000707 0xf5fffffff1e00038

def z952 : W := mkw 0x5dd98963f2746a4a 0xa2eecc4b1f93a352 0x99919b67c0707800 0x44cc8cdb3e0383c0

def z953 : W := mkw 0x222664980d8b85b5 0x41113324c06c5c2d 0xe66e64993f8fe7ff 0xff337324c9fc7f3f

def z954 : W := mkw 0x5ddb8001fb6c0018 0x02eedc000fdb6000 0x7fff8000fffe0013 0xa3fffc0007fff000

def z955 : W := mkw 0x4082812b6b7e637a 0x220414095b5bf31b 0x4000000123fe67e8 0x0a000000091ff33f

def z956 : W := mkw 0x17845711b4015606 0x00bc22b88da00ab0 0xbf8e7f19fc01ff1e 0xfdfc73f8cfe00ff8

def z957 : W := mkw 0x0080812b2036636a 0x200404095901b31b 0xc19187ff207e67ec 0x4e0c8c3ff903f33f

def z958 : W := mkw 0x9f7d7ed400000000 0x04fbebf6a0000000 0xfffffffe0380001f 0xf7fffffff01c0000

def z959 : W := mkw 0x887d28d400000000 0x0443e946a0000000 0xb9fffffe00000007 0xf5cffffff0000000

def z960 : W := mkw 0x5ddb8001fb6c0018 0x02eedc000fdb6000 0x7fff80fffffe001b 0xf3fffc07fffff000

def z961 : W := mkw 0x222664980d8b85b5 0x41113324c06c5c2d 0x666e64983f8f87e7 0x8b337324c1fc7c3f

def z962 : W := mkw 0x5ddb8001fb6c0018 0x02eedc000fdb6000 0x7fef8001fffe001a 0xa3ff7c000ffff000

def z963 : W := mkw 0x0080812bb036736a 0x200404095d81b39b 0xc19187ffe07e7fef 0xde0c8c3fff03f3ff

def z964 : W := mkw 0x0082812b293e637a 0x200414095949f31b 0x400000013ffe67f8 0x0a00000009fff33f

def z965 : W := mkw 0x222465ba0493e7e7 0x6111232dd0249f3f 0x000064980001e7e4 0x08000324c0000f3f

def z966 : W := mkw 0x0200570004015606 0x001002b800200ab0 0x9e007f01fc01ff1c 0xfcf003f80fe00ff8

def z967 : W := mkw 0x9d7d3ad400000000 0x04ebe9d6a0000000 0xbfff9bfe00000003 0xf5fffcdff0000000

def z968 : W := mkw 0x222664980d8b85b5 0x41113324c06c5c2d 0x666e64983f8f87fc 0x2b337324c1fc7c3f

def z969 : W := mkw 0x9f7d7ed400000000 0x04fbebf6a0000000 0xfffffffe000000ef 0xfffffffff0000007

def z970 : W := mkw 0x5ddb8001fb6c0018 0x02eedc000fdb6000 0xfffff801fffe001f 0xf7ffffc00ffff000

def z971 : W := mkw 0x9f7d7ed442400000 0x04fbebf6a2120000 0xffffffffc3f1f81f 0xfffffffffe1f8fc0

def z972 : W := mkw 0x972d769400000000 0x04b96bb4a0000000 0xa7ffe7fe00000007 0xf53fff3ff0000000

def z973 : W := mkw 0x9f7d7ed442c08881 0x84fbebf6a2160444 0xffffffffc3f1981f 0xf7fffffffe1f8cc0

def z974 : W := mkw 0x0080812b2036636a 0x200404095901b31b 0xc19187ffe07fffff 0xde0c8c3fff03ffff

def z975 : W := mkw 0xdddb8845fb6c0018 0x06eedc422fdb6000 0x7fff8067fffe001b 0xf3fffc033ffff000

def z976 : W := mkw 0x9f7d7ed400808881 0x84fbebf6a0040444 0xbffffffe00019807 0xf5fffffff0000cc0

def z977 : W := mkw 0x5ddb8841fb6c0818 0x82eedc420fdb6040 0x7fff9801fffe181b 0xf3fffcc00ffff0c0

def z978 : W := mkw 0x17805701b4015606 0x00bc02b80da00ab0 0x1f807801fc01ff18 0xf8fc03c00fe00ff8

def z979 : W := mkw 0x222664980d8b85b5 0x41113324c06c5c2d 0x666e64183f8f87fa 0xab337320c1fc7c3f

def z980 : W := mkw 0x0080812b2036636a 0x200404095901b31b 0xe7ff87ff207e67ef 0xff3ffc3ff903f33f

def z981 : W := mkw 0x087028e042d0a8c1 0x8043814702168546 0xd9f1fbe7c3f1f8fd 0x7ecf8fdf3e1f8fc7

def z982 : W := mkw 0x087028e042d0a8c1 0x8043814702168546 0xd8707ce1e3f1fffd 0xfec383e70f1f8fff

def z983 : W := mkw 0x287228e84bdaa9f1 0xc1439147425ed54f 0x407000e003fe00e1 0x02038007001ff007

def z984 : W := mkw 0x17805701b4015606 0x00bc02b80da00ab0 0x9f807ffffc01ff1c 0xfcfc03ffffe00ff8

def z985 : W := mkw 0x0080812b2036636a 0x200404095901b31b 0x419187ff207e67eb 0x8a0c8c3ff903f33f

def z986 : W := mkw 0x9f5d5e5400000000 0x04faeaf2a0000000 0x279f877e00000002 0x813cfc3bf0000000

def z987 : W := mkw 0x5d5b8000db6c0018 0x02eadc0006db6000 0x7fff8000dffe0013 0xf3fffc0006fff000

def z988 : W := mkw 0x9f7d7ed400000000 0x04fbebf6a0000000 0xbffffffe0001801f 0xfdfffffff0000c00

def z989 : W := mkw 0x087028e042d0a8c1 0x8043814702168546 0xd87078e1c3f1f8e5 0x4ec383c70e1f8fc7

def z990 : W := mkw 0x1780d701b425560e 0x00bc06b80da12ab0 0x9f91ff01fc71ff1c 0xfcfc8ff80fe38ff8

def z991 : W := mkw 0x087028e042d0a8c1 0x8043814702168546 0xd81078e1c3f1f8fc 0x4ec083c70e1f8fc7

def z992 : W := mkw 0x9f7d7ed442c08081 0x04fbebf6a2160404 0xffffffffc3f180ff 0xfffffffffe1f8c07

def z993 : W := mkw 0x5d5b8000db6c0018 0x02eadc0006db6000 0x7e7f8001dffe001b 0x73f3fc000efff000

def z994 : W := mkw 0x0850002042d0a8c1 0x8042800102168546 0xd8707801c3f1f8fd 0x7ec383c00e1f8fc7

def z995 : W := mkw 0x9f7d7ed400000000 0x04fbebf6a0000000 0xa7fffffe00000007 0x853ffffff0000000

def z996 : W := mkw 0x8a7d7ed400000000 0x0453ebf6a0000000 0xa1fffffe00000007 0xd50ffffff0000000

def z997 : W := mkw 0x222676980d8b95b5 0x411133b4c06c5cad 0x666e7c983f8f9fff 0xbb3373e4c1fc7cff

def z998 : W := mkw 0x9f7d7ed400000000 0x04fbebf6a0000000 0xbffffffe00000004 0x65fffffff0000000

def z999 : W := mkw 0x17805701b4015606 0x00bc02b80da00ab0 0x99807f01fc01ff1c 0x4ccc03f80fe00ff8

def z1000 : W := mkw 0x222464b80493ade5 0xc1112325c0249d6f 0x000064980001ffe4 0x08000324c0000fff

def z1001 : W := mkw 0x2082812b29bee3fb 0x61041409594df71f 0x4000000123fe67e8 0x0a000000091ff33f

def z1002 : W := mkw 0x222664980d8b85b5 0x41113324c06c5c2d 0x266e64983f8f87f6 0xa9337324c1fc7c3f

def z1003 : W := mkw 0x17805701b4015606 0x00bc02b80da00ab0 0x1e007c01fc01ff1c 0xb8f003e00fe00ff8

def z1004 : W := mkw 0x15801301b4015606 0x00ac00980da00ab0 0x99807b01fc01ff1c 0x7ccc03d80fe00ff8

def z1005 : W := mkw 0x5ddb8001fb6c0018 0x02eedc000fdb6000 0x7fff8001fffff81b 0xfbfffc000fffffc0

def z1006 : W := mkw 0x087028e042d0a8c1 0x8043814702168546 0xd8707861c3f1f8f8 0x6ec383c30e1f8fc7

def z1007 : W := mkw 0x1700560004010404 0x00b802b000200820 0x9f807f01fc01ff1c 0xfcfc03f80fe00ff8

def z1008 : W := mkw 0x9f7d7ed442400000 0x04fbebf6a2120000 0xbfffffffc0700007 0xf5fffffffe038000

def z1009 : W := mkw 0x087028e042d0a8c1 0x8043814702168546 0x987078e1c3f1f8f4 0x6cc383c70e1f8fc7

def z1010 : W := mkw 0x9f7d7ed400000000 0x04fbebf6a0000000 0xbfeffffe00000006 0xa5ff7ffff0000000

def z1011 : W := mkw 0x222664980d8b85b5 0x41113324c06c5c2d 0x666e60803f8f87fd 0x3b33730401fc7c3f

def z1012 : W := mkw 0x9f5d5e5400000000 0x04faeaf2a0000000 0xbf9fff7e00000006 0xf5fcfffbf0000000

def z1013 : W := mkw 0x9f7d7ed400000000 0x04fbebf6a0000000 0xbffffffe2000070f 0xfdfffffff1000038

def z1014 : W := mkw 0x5ddb8101fb6c421a 0x02eedc080fdb6210 0xffff8301fffe601b 0xf7fffc180ffff300

def z1015 : W := mkw 0x8a7d6cd400000000 0x0453eb66a0000000 0xa7ffe7fe00000007 0xf53fff3ff0000000

def z1016 : W := mkw 0x0080812b2036636a 0x200404095901b31b 0x819187ff207e67e6 0xcc0c8c3ff903f33f

def z1017 : W := mkw 0x5ddb8001fb6c0018 0x02eedc000fdb6000 0x7fff871ffffe001b 0xf3fffc38fffff000

def z1018 : W := mkw 0x1ddb8001292c0018 0x00eedc0009496000 0x7fff80013ffe001b 0xf3fffc0009fff000

def z1019 : W := mkw 0x17805701b4015606 0x00bc02b80da00ab0 0x9f807f01fc01ff04 0xccfc03f80fe00ff8

def z1020 : W := mkw 0x0000812a0036636a 0x200004095001b31b 0xc19187fe007e67e7 0xde0c8c3ff003f33f

def z1021 : W := mkw 0x9f7d7ed404010404 0x04fbebf6a0200820 0xbffffffe1c018017 0xf5fffffff0e00c00

def z1022 : W := mkw 0x5ddb8001fb6c0018 0x02eedc000fdb6000 0x7fee0001fffe0018 0xf3ff70000ffff000

def z1023 : W := mkw 0x9f7d7ed404010404 0x04fbebf6a0200820 0xbffffffffc01ff1f 0xfdffffffffe00ff8

def z1024 : W := mkw 0x4082812bb93e637a 0x220414095dc9f31b 0x400000013c7e67e8 0x0a00000009e3f33f

def z1025 : W := mkw 0x5ddb9201fb6c0018 0x02eedc900fdb6000 0xffff9b01fffe001b 0xf7fffcd80ffff000

def z1026 : W := mkw 0x0850086042d0a8c1 0x8042804302168546 0xd8107861c3f1f8fc 0x7ec083c30e1f8fc7

def z1027 : W := mkw 0x5ddb8001fb6c0018 0x02eedc000fdb6000 0x7fff8001dffe0013 0x63fffc000efff000

def z1028 : W := mkw 0x1f7d649000000000 0x00fbeb2480000000 0xbfffe7fe00000007 0xf5ffff3ff0000000

def z1029 : W := mkw 0x17805701b4015606 0x00bc02b80da00ab0 0x9f91ff67fc01ff1c 0xfcfc8ffb3fe00ff8

def z1030 : W := mkw 0x17805701b4015606 0x00bc02b80da00ab0 0xdfe07f01ff81ff1d 0xfeff03f80ffc0ff8

def z1031 : W := mkw 0x97895705b4015606 0x04bc4ab82da00ab0 0x9f81ff07fc01ff1c 0xfcfc0ff83fe00ff8

def z1032 : W := mkw 0x220644180d8b85b5 0x41103220c06c5c2d 0x666e04183f8f87fb 0xbb337020c1fc7c3f

def z1033 : W := mkw 0x0080812b2036636a 0x200404095901b31b 0xc19187ff007e67e7 0x4e0c8c3ff803f33f

def z1034 : W := mkw 0x2876a8fa4bfea9f9 0xe143b547d25ff54f 0x607f80fe03fe00e3 0x0303fc07f01ff007

def z1035 : W := mkw 0x1780d701b425560e 0x00bc06b80da12ab0 0xdf807f01fc7fff1c 0xfefc03f80fe3fff8

def z1036 : W := mkw 0x002028e042d0a8c1 0x8001014702168546 0xd80078e1c3f1f8fc 0x7ec003c70e1f8fc7

def z1037 : W := mkw 0x48d28001fb6c0018 0x024694000fdb6000 0x7e7e0001fffe001b 0xf3f3f0000ffff000

def z1038 : W := mkw 0x5ddb8001fb6c0018 0x02eedc000fdb6000 0x7fff8401fffe071f 0xfbfffc200ffff038

def z1039 : W := mkw 0x0080812b2036636a 0x200404095901b31b 0xc1f187ff23fe67ff 0xfe0f8c3ff91ff33f

def z1040 : W := mkw 0x222676980d8b85b5 0x411133b4c06c5c2d 0xe66e7f983f8f87ff 0xbf3373fcc1fc7c3f

def z1041 : W := mkw 0x6082812bffffe7ff 0x630414095fffff3f 0x40000001ffffe7f8 0x0a0000000fffff3f

def z1042 : W := mkw 0x222664980d8b85b5 0x41113324c06c5c2d 0x67efe79e3f8f87ff 0xbb3f7f3cf1fc7c3f

def z1043 : W := mkw 0x222477ba0493f7e7 0x611123bdd0249fbf 0x80007ffe0001ffe4 0x0c0003fff0000fff

def z1044 : W := mkw 0x5ddb8001fb6c0018 0x02eedc000fdb6000 0x7e6e0001fffe001b 0xb3f370000ffff000

def z1045 : W := mkw 0x087028e042d0a8c1 0x8043814702168546 0xde7078e1fff1f8fd 0xfef383c70fff8fc7

def z1046 : W := mkw 0x222664980d8b85b5 0x41113324c06c5c2d 0xe66e67fe3f8f87ff 0xbf33733ff1fc7c3f

def z1047 : W := mkw 0x087028e042d0a8c1 0x8043814702168546 0xd87078e1e3fff8ff 0xfec383c70f1fffc7

def z1048 : W := mkw 0x5ddb8001fb6c0018 0x02eedc000fdb6000 0x7fffe001ffff801f 0xfbffff000ffffc00

def z1049 : W := mkw 0x5dd98123f274624a 0x22eecc091f93a312 0x19918001c0706000 0x40cc8c000e038300

def z1050 : W := mkw 0x22266cd80d8b85b5 0x41113366c06c5c2d 0xe66e7cf83f8f87ff 0xbf3373e7c1fc7c3f

def z1051 : W := mkw 0x00222088098a81b1 0x00011104404c540d 0x666e64983f8f87ff 0xbb337324c1fc7c3f

def z1052 : W := mkw 0x087028e042d0a8c1 0x8043814702168546 0xd8607801c3f1f8fc 0x7ec303c00e1f8fc7

def z1053 : W := mkw 0x1d7928c000000000 0x00ebc94600000000 0xbffffffe00000007 0xf5fffffff0000000

def z1054 : W := mkw 0x9f7d7ed400000000 0x04fbebf6a0000000 0xbfffffffc000001f 0xf5fffffffe000000

def z1055 : W := mkw 0x17804401b4010404 0x00bc02200da00820 0x9f807c01fc01ff1c 0xfcfc03e00fe00ff8

def z1056 : W := mkw 0x778fd719bd2f573e 0x43bc7eb8cde97ab9 0x278f87183c0e0702 0x813c7c38c1e07038

def z1057 : W := mkw 0x17805701b4015606 0x00bc02b80da00ab0 0x9f81ff1ffc01ff1e 0xfcfc0ff8ffe00ff8

def z1058 : W := mkw 0x9d7d3ad400000000 0x04ebe9d6a0000000 0x21ff83fe00000003 0x010ffc1ff0000000

def z1059 : W := mkw 0x0000002042d0a8c1 0x8000000102168546 0xd81078e1c3f1f8fd 0x7ec083c70e1f8fc7

def z1060 : W := mkw 0x002020a00090a0c1 0x0001010500048506 0xd87078e1c3f1f8fd 0x7ec383c70e1f8fc7

def z1061 : W := mkw 0xdddb9b45fb6c521a 0x06eedcda2fdb6290 0xffff9b67fffe781b 0xf7fffcdb3ffff3c0

def z1062 : W := mkw 0x17805701b4015606 0x00bc02b80da00ab0 0x9f807f01fc01ff10 0xe4fc03f80fe00ff8

def z1063 : W := mkw 0x17805701b4015606 0x00bc02b80da00ab0 0xdf907f01fc71ff1d 0xfefc83f80fe38ff8

def z1064 : W := mkw 0x02804501b4015606 0x001402280da00ab0 0x9e007c01fc01ff1c 0xfcf003e00fe00ff8

def z1065 : W := mkw 0x000200004b480010 0x00001000025a4000 0x666e0001fffe001b 0xb33370000ffff000

def z1066 : W := mkw 0x5ddb8001fb6c0018 0x02eedc000fdb6000 0xffff80e1fffe001f 0xf7fffc070ffff000

def z1067 : W := mkw 0x1700560094011404 0x00b802b004a008a0 0x9e007c01fc01ff1c 0xfcf003e00fe00ff8

def z1068 : W := mkw 0x222664980d8b85b5 0x41113324c06c5c2d 0xe7ee67983f8f87ff 0xff3f733cc1fc7c3f

def z1069 : W := mkw 0x1509000000000000 0x00a8480000000000 0xa79f87fe00000007 0xd53cfc3ff0000000

def z1070 : W := mkw 0x9d591a4400000000 0x04eac8d220000000 0xbfff9ffe00000007 0xf5fffcfff0000000

def z1071 : W := mkw 0x22266cd80d8b8db5 0xc1113366c06c5c6d 0x666e7c983f8f9fff 0xbb3373e4c1fc7cff

def z1072 : W := mkw 0x5ddb8103fb6c421a 0x22eedc081fdb6210 0x7fff8307fffe001b 0xf3fffc183ffff000

def z1073 : W := mkw 0x200200080d8b85b5 0x41001000406c5c2d 0x666e04983f8f87ff 0xbb337024c1fc7c3f

def z1074 : W := mkw 0x087928e042d0a8c1 0x8043c94702168546 0xf87ff8e1c3f1f8ff 0x7fc3ffc70e1f8fc7

def z1075 : W := mkw 0x5ddb8001fb6c0018 0x02eedc000fdb6000 0xffff8367fffe001b 0xf7fffc1b3ffff000

def z1076 : W := mkw 0x1700570094015606 0x00b802b804a00ab0 0x9e007f01dc01ff1c 0x7cf003f80ee00ff8

def z1077 : W := mkw 0x5ddb8001fb6c0018 0x02eedc000fdb6000 0x3fff8001fffe0012 0xe1fffc000ffff000

def z1078 : W := mkw 0x5ddb8001fb6c0018 0x02eedc000fdb6000 0x7ffff801ffff981b 0xf3ffffc00ffffcc0

def z1079 : W := mkw 0x4082812bff7f777e 0x220414095ffbfbbb 0x40000001fffffff8 0x0a0000000fffffff

def z1080 : W := mkw 0x5d5b0000db480010 0x02ead80006da4000 0x7e7e0001fffe001b 0xf3f3f0000ffff000

def z1081 : W := mkw 0x9f7d7ed4d6c19c85 0x84fbebf6a6b60ce4 0xbffffffedf819817 0xf5fffffff6fc0cc0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z1,z8,z2,z3,z4,z6]),(0,[z9,z0,z1,z2,z3,z10,z6]),(0,[z0,z1,z2,z3,z11,z4,z6]),(0,[z0,z1,z2,z12,z3,z4,z6]),(0,[z0,z1,z13,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z14,z4,z15])],[(0,[z16,z0,z1,z2,z3,z4,z6]),(0,[z17,z0,z1,z2,z3,z4,z6]),(0,[z18,z0,z1,z2,z3,z19,z6])],[(0,[z20,z1,z8,z2,z3,z4,z6]),(0,[z21,z0,z1,z2,z3,z4,z22]),(0,[z21,z0,z1,z2,z3,z4,z23]),(0,[z21,z0,z1,z2,z24,z3,z4]),(0,[z0,z1,z2,z3,z4,z25,z26]),(0,[z0,z1,z2,z3,z14,z4,z25])],[(0,[z0,z1,z2,z27,z3,z4,z6])],[(0,[z28,z18,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z25,z29]),(0,[z0,z1,z2,z30,z3,z14,z6])],[(0,[z31,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z32,z3,z4,z6]),(0,[z33,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z34,z29]),(0,[z0,z1,z2,z3,z4,z6,z35])],[(0,[z0,z1,z2,z3,z4,z6,z36]),(0,[z37,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z10,z4,z6]),(0,[z38,z0,z1,z2,z3,z39,z6]),(0,[z0,z1,z2,z40,z3,z4,z6]),(0,[z0,z1,z2,z3,z41,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z6,z42]),(0,[z0,z1,z2,z43,z3,z4,z6]),(0,[z0,z1,z2,z44,z3,z4,z6])],[],[(0,[z45,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z46,z4,z6]),(0,[z21,z0,z1,z2,z3,z14,z4]),(0,[z47,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z48,z3,z4,z6]),(0,[z0,z1,z49,z3,z4,z6,z50])],[(0,[z0,z1,z2,z3,z4,z51,z6]),(0,[z0,z1,z2,z3,z4,z52,z6])],[(0,[z53,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z54,z4,z6]),(0,[z0,z1,z2,z55,z3,z4,z6]),(0,[z0,z56,z57,z2,z3,z4,z6])],[(0,[z58,z28,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z4,z59,z6]),(0,[z60,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z61,z4,z6]),(0,[z9,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z62,z4,z6]),(0,[z0,z1,z2,z3,z4,z26,z34]),(0,[z0,z1,z2,z3,z4,z63,z6])],[(0,[z64,z0,z1,z3,z4,z6,z50]),(0,[z0,z1,z2,z65,z3,z4,z6]),(0,[z0,z1,z66,z2,z3,z4,z6]),(0,[z18,z0,z1,z2,z3,z67,z6]),(0,[z0,z68,z1,z2,z4,z6,z69])]],
   [[(0,[z70,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z71,z3,z4,z6]),(0,[z0,z1,z2,z72,z3,z4,z6]),(0,[z0,z1,z2,z73,z3,z4,z6])],[(0,[z0,z1,z2,z3,z39,z74,z6]),(0,[z0,z1,z2,z3,z75,z4,z6])],[(0,[z76,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z77,z3,z4,z6]),(0,[z78,z0,z1,z2,z3,z4,z6]),(0,[z0,z57,z2,z3,z4,z6,z29]),(0,[z18,z0,z79,z2,z3,z4,z6])],[(0,[z80,z0,z1,z81,z3,z4,z6]),(1,[z38,z1,z2,z3,z39,z6]),(0,[z82,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z83,z4,z6]),(0,[z0,z1,z2,z84,z3,z4,z6])],[(0,[z0,z7,z1,z2,z3,z4,z85]),(0,[z21,z0,z1,z2,z3,z86,z6]),(0,[z0,z1,z87,z2,z3,z4,z6]),(1,[z88,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z89,z6]),(0,[z0,z1,z2,z3,z4,z6,z90])],[(0,[z0,z1,z2,z91,z3,z4,z6])],[(0,[z0,z1,z2,z3,z39,z6,z15]),(0,[z0,z1,z2,z3,z4,z6,z92]),(0,[z0,z1,z2,z3,z93,z4,z6]),(0,[z0,z1,z2,z94,z3,z4,z6]),(0,[z0,z1,z2,z3,z95,z4,z6])],[(0,[z96,z0,z1,z2,z3,z4,z6]),(0,[z0,z97,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z98,z3,z4,z6]),(0,[z28,z0,z79,z1,z2,z3,z6]),(0,[z0,z99,z1,z2,z3,z4,z6]),(0,[z0,z68,z1,z2,z3,z4,z34])]],
   [[(0,[z0,z100,z1,z2,z3,z101,z6]),(0,[z0,z1,z2,z3,z102,z4,z6]),(0,[z0,z103,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z14,z4,z6])],[(0,[z104,z0,z1,z2,z3,z4,z6]),(0,[z38,z0,z1,z105,z3,z4,z6]),(0,[z106,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z107,z3,z108,z4,z6]),(0,[z0,z1,z2,z109,z3,z4,z6]),(0,[z110,z0,z1,z2,z3,z4,z6])],[(0,[z0,z111,z1,z2,z3,z4,z6])],[(0,[z0,z112,z1,z2,z3,z4,z6]),(0,[z113,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z114]),(0,[z115,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z116,z3,z4,z6])],[(0,[z117,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z118,z6])],[(0,[z119,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z120,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z121,z4,z6])],[(1,[z0,z1,z2,z3,z10,z6]),(0,[z0,z1,z2,z3,z4,z6,z122]),(0,[z0,z1,z2,z3,z123,z4,z6]),(0,[z0,z1,z2,z84,z3,z124,z6])],[(0,[z0,z1,z2,z3,z125,z4,z6]),(0,[z1,z126,z2,z81,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z127,z6]),(0,[z0,z1,z2,z3,z4,z128,z6]),(0,[z96,z0,z1,z2,z3,z4,z129]),(0,[z0,z1,z2,z3,z4,z130,z6]),(0,[z131,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z132,z45,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z133,z6]),(0,[z64,z134,z0,z2,z3,z4,z6]),(0,[z135,z0,z1,z2,z3,z4,z136]),(0,[z137,z0,z1,z2,z3,z4,z6])],[(0,[z0,z138,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z139,z4,z39])],[(0,[z140,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z141,z2,z3,z4,z6]),(0,[z0,z1,z2,z142,z3,z4,z6]),(0,[z0,z79,z1,z2,z3,z4,z143]),(0,[z0,z1,z2,z3,z4,z144,z6]),(0,[z145,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z146,z6]),(0,[z0,z1,z2,z3,z4,z6,z147])],[(0,[z0,z1,z2,z148,z3,z4,z6]),(0,[z0,z149,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z150,z4,z6])],[(0,[z20,z45,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z151,z6])],[(0,[z96,z0,z1,z2,z3,z4,z26]),(0,[z80,z0,z56,z1,z3,z4,z6])],[(0,[z0,z1,z2,z3,z152,z4,z6]),(1,[z0,z1,z2,z153,z3,z4]),(0,[z0,z1,z2,z3,z4,z6,z154]),(0,[z0,z1,z2,z3,z46,z6,z15]),(0,[z155,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z156,z3,z4,z6]),(0,[z157,z0,z1,z2,z3,z4,z6]),(0,[z0,z158,z1,z2,z3,z4,z6]),(0,[z0,z1,z159,z2,z107,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z160])],[(0,[z1,z8,z2,z81,z3,z4,z6]),(0,[z0,z1,z2,z3,z161,z4,z6]),(0,[z0,z162,z1,z2,z3,z4,z6]),(0,[z0,z163,z1,z2,z3,z4,z6]),(1,[z135,z0,z2,z164,z4,z6]),(0,[z0,z1,z3,z165,z164,z4,z6]),(0,[z0,z1,z159,z2,z3,z52,z6]),(0,[z166,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z167,z4,z6]),(0,[z0,z111,z1,z2,z3,z4,z26]),(0,[z0,z1,z2,z3,z4,z6,z168]),(0,[z0,z1,z169,z2,z3,z4,z6])],[(0,[z170,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z171]),(0,[z0,z1,z2,z3,z4,z172,z6]),(0,[z0,z1,z49,z2,z3,z4,z50])],[(1,[z0,z1,z2,z3,z4,z143]),(0,[z0,z111,z1,z2,z3,z4,z29]),(0,[z0,z1,z2,z84,z3,z74,z6]),(0,[z0,z173,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z174])],[(1,[z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z105,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z26,z15]),(0,[z0,z1,z175,z2,z3,z4,z6]),(0,[z0,z1,z176,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z177,z6]),(0,[z0,z1,z2,z3,z4,z6,z50]),(0,[z0,z1,z2,z3,z4,z6,z178])],[(0,[z0,z1,z2,z3,z4,z179,z6]),(0,[z180,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z181,z4,z6]),(0,[z182,z0,z1,z2,z3,z4,z6]),(0,[z183,z0,z1,z2,z3,z4,z6])],[(0,[z184,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z185,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z186,z6]),(0,[z0,z1,z2,z84,z3,z6,z15])]],
   [[(0,[z187,z0,z1,z2,z3,z4,z6]),(0,[z188,z38,z1,z2,z3,z4,z6]),(0,[z0,z189,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z190,z6])],[(0,[z0,z1,z2,z3,z4,z6,z191]),(0,[z192,z0,z1,z2,z3,z4,z6]),(0,[z21,z0,z193,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z194,z6]),(0,[z0,z195,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z196])],[(0,[z0,z7,z1,z2,z3,z4,z197]),(0,[z0,z1,z2,z84,z3,z14,z6])],[(0,[z135,z0,z1,z2,z164,z4,z6]),(0,[z134,z0,z2,z3,z4,z26,z6]),(0,[z0,z195,z1,z2,z108,z4,z6]),(0,[z198,z0,z1,z2,z3,z4,z6]),(0,[z0,z199,z1,z2,z3,z4,z6])],[(0,[z45,z1,z2,z81,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z67,z6]),(0,[z200,z0,z2,z3,z4,z23,z6])],[(0,[z0,z1,z2,z3,z4,z201,z6]),(0,[z188,z0,z1,z2,z84,z3,z6]),(0,[z202,z0,z1,z2,z3,z4,z6]),(0,[z203,z0,z1,z2,z3,z4,z6])],[(1,[z0,z1,z2,z3,z204,z6]),(1,[z0,z163,z2,z205,z4,z6]),(0,[z0,z1,z2,z84,z3,z206,z6]),(0,[z0,z1,z2,z3,z207,z4,z6])],[(0,[z208,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z209,z4,z6]),(0,[z210,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z50,z69])]],
   [[(0,[z9,z1,z2,z81,z3,z4,z6]),(0,[z0,z1,z2,z211,z3,z4,z6]),(0,[z0,z1,z2,z212,z3,z4,z6]),(0,[z213,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z214,z4,z6]),(0,[z0,z1,z2,z3,z215,z4,z6])],[(0,[z21,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z86,z6]),(0,[z18,z0,z1,z2,z3,z4,z6])],[(0,[z0,z111,z2,z3,z4,z6,z29]),(0,[z0,z1,z2,z3,z4,z29,z15]),(0,[z0,z1,z159,z2,z3,z216,z6])],[(0,[z0,z1,z3,z217,z4,z74,z6]),(0,[z0,z1,z3,z4,z23,z6,z50]),(0,[z28,z0,z1,z2,z4,z124,z6]),(0,[z0,z1,z2,z218,z3,z4,z6])],[(0,[z219,z0,z1,z2,z3,z4,z6]),(0,[z0,z220,z1,z2,z3,z4,z6])],[(0,[z221,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z181,z4,z6]),(1,[z0,z1,z222,z3,z74,z6]),(0,[z0,z223,z1,z2,z3,z4,z6]),(0,[z0,z224,z1,z2,z3,z4,z6])],[(0,[z225,z0,z1,z2,z3,z4,z6]),(0,[z226,z1,z2,z32,z3,z4,z6]),(0,[z21,z0,z1,z227,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z228,z6]),(0,[z0,z2,z3,z19,z4,z67,z6]),(0,[z0,z1,z222,z2,z3,z217,z6]),(0,[z229,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z8,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z230]),(0,[z80,z0,z1,z126,z3,z4,z6]),(0,[z21,z0,z1,z231,z3,z4,z6]),(0,[z0,z163,z2,z205,z3,z4,z6])]],
   [[(0,[z0,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z232,z4,z6]),(0,[z0,z233,z1,z2,z3,z4,z6]),(0,[z0,z234,z1,z2,z3,z4,z6])],[(0,[z132,z1,z8,z2,z3,z4,z6]),(0,[z38,z0,z1,z2,z84,z3,z6]),(0,[z0,z1,z2,z235,z3,z4,z6]),(0,[z188,z28,z0,z1,z2,z3,z6]),(0,[z21,z0,z1,z2,z3,z4,z129]),(0,[z0,z1,z2,z3,z4,z236,z6])],[(0,[z132,z0,z1,z2,z3,z4,z6]),(0,[z28,z226,z0,z1,z2,z4,z6]),(0,[z0,z1,z237,z2,z3,z4,z6]),(0,[z96,z0,z68,z1,z2,z3,z4]),(0,[z0,z238,z1,z2,z3,z4,z6])],[(0,[z0,z239,z1,z2,z3,z4,z6]),(0,[z240,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z217,z46,z6]),(0,[z0,z1,z2,z241,z3,z4,z6]),(0,[z0,z1,z2,z3,z216,z4,z6]),(0,[z80,z0,z1,z3,z4,z23,z6]),(0,[z0,z1,z2,z24,z3,z4,z69]),(0,[z0,z242,z1,z2,z3,z4,z6])],[(0,[z0,z243,z1,z2,z3,z4,z6]),(0,[z0,z244,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z26,z6]),(0,[z245,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z246,z3,z4,z6])],[(0,[z20,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z247,z3,z4,z6]),(0,[z0,z1,z2,z248,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z85]),(0,[z134,z0,z7,z2,z3,z4,z6]),(0,[z0,z1,z2,z249,z3,z4,z6]),(0,[z0,z1,z2,z250,z3,z4,z6]),(0,[z0,z1,z2,z251,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z252,z6]),(0,[z0,z1,z2,z3,z4,z253,z6]),(0,[z0,z1,z254,z2,z3,z4,z6]),(0,[z0,z1,z2,z255,z3,z4,z6]),(0,[z0,z1,z2,z3,z256,z4,z6])],[(0,[z0,z1,z2,z3,z4,z129,z6]),(0,[z21,z0,z1,z2,z3,z4,z26]),(0,[z0,z1,z2,z3,z4,z6,z257]),(0,[z0,z1,z2,z3,z4,z6,z258])]],
   [[(0,[z0,z1,z259,z2,z3,z4,z6]),(0,[z58,z1,z2,z3,z101,z4,z6]),(0,[z0,z1,z2,z3,z260,z4,z6]),(0,[z0,z1,z261,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z262,z6]),(0,[z21,z0,z1,z2,z3,z4,z29]),(1,[z263,z1,z2,z3,z4,z6]),(0,[z0,z1,z264,z2,z3,z4,z6]),(0,[z265,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z266]),(0,[z0,z1,z2,z3,z4,z6,z267])],[(0,[z268,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z269,z6]),(0,[z0,z1,z2,z3,z4,z6,z270]),(1,[z0,z1,z2,z4,z6,z271])],[(0,[z272,z0,z1,z2,z3,z4,z6]),(0,[z0,z273,z1,z81,z3,z4,z6]),(0,[z0,z1,z2,z274,z4,z39,z6]),(0,[z0,z1,z2,z3,z19,z74,z6]),(0,[z275,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z276,z3,z4,z6])],[(0,[z277,z0,z1,z2,z3,z4,z6]),(0,[z226,z0,z1,z2,z206,z4,z6]),(0,[z0,z1,z2,z3,z278,z4,z6]),(0,[z0,z1,z279,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z280])],[(0,[z0,z1,z2,z3,z4,z281,z6]),(0,[z0,z282,z1,z2,z3,z4,z6]),(0,[z58,z0,z1,z2,z101,z4,z6]),(0,[z0,z56,z1,z2,z3,z4,z6]),(0,[z0,z283,z1,z2,z3,z4,z6]),(0,[z0,z68,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z284]),(1,[z0,z1,z49,z3,z4,z50]),(0,[z0,z1,z2,z3,z285,z4,z6])],[(1,[z0,z1,z2,z286,z3,z6]),(0,[z0,z1,z2,z3,z217,z19,z6]),(0,[z287,z0,z1,z2,z3,z4,z6]),(0,[z288,z0,z1,z2,z3,z4,z6])]],
   [[],[(1,[z0,z1,z2,z3,z4,z136]),(0,[z289,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z290,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z291,z6])],[(0,[z0,z1,z2,z292,z3,z4,z6]),(0,[z0,z1,z2,z293,z3,z4,z6]),(0,[z0,z294,z1,z2,z3,z4,z6]),(1,[z200,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z295])],[(0,[z0,z1,z296,z2,z3,z4,z6]),(0,[z21,z1,z2,z3,z4,z6,z22]),(0,[z0,z2,z205,z3,z164,z4,z6])],[(1,[z226,z1,z2,z32,z4,z6]),(1,[z21,z1,z2,z3,z4,z22]),(0,[z0,z1,z2,z3,z4,z297,z6]),(0,[z0,z1,z2,z3,z4,z6,z298])],[(0,[z0,z1,z299,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z300,z6]),(0,[z0,z301,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z302,z4,z6]),(1,[z0,z2,z3,z4,z303,z6])],[(0,[z21,z0,z1,z2,z30,z3,z4]),(0,[z0,z1,z2,z3,z4,z23,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z304,z6]),(0,[z0,z305,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z306,z6]),(0,[z0,z1,z307,z2,z3,z4,z6]),(0,[z0,z1,z222,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z308]),(0,[z0,z1,z2,z3,z4,z6,z271])],[(0,[z0,z1,z231,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z309,z6]),(0,[z310,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z22]),(0,[z135,z0,z163,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z311,z6]),(1,[z0,z1,z2,z3,z4,z35]),(0,[z0,z1,z2,z3,z312,z4,z6])],[(0,[z313,z0,z1,z2,z3,z4,z6]),(0,[z0,z263,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z217,z67,z6])],[(0,[z0,z314,z1,z2,z3,z4,z6]),(0,[z188,z0,z1,z2,z3,z46,z6]),(0,[z0,z2,z3,z4,z26,z6,z29]),(0,[z0,z1,z2,z3,z4,z315,z6])],[(0,[z0,z314,z1,z2,z3,z101,z4]),(0,[z0,z163,z1,z2,z164,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z316]),(0,[z200,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z7,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z317]),(0,[z0,z1,z222,z3,z4,z74,z6]),(0,[z318,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z319,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z320]),(0,[z0,z1,z2,z3,z4,z321,z6])],[(0,[z0,z1,z322,z2,z3,z4,z6]),(0,[z0,z323,z1,z2,z3,z4,z6]),(0,[z64,z0,z1,z2,z324,z4,z6]),(0,[z135,z0,z1,z2,z205,z4,z6]),(0,[z0,z1,z2,z325,z3,z4,z6]),(0,[z0,z1,z2,z3,z326,z4,z6]),(0,[z0,z1,z2,z327,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z328]),(0,[z0,z1,z2,z3,z4,z329,z6])],[],[(0,[z0,z1,z2,z3,z46,z74,z6]),(0,[z21,z0,z68,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z266,z6]),(0,[z0,z1,z2,z3,z4,z330,z6]),(0,[z0,z1,z2,z3,z4,z23,z34]),(0,[z331,z0,z1,z2,z3,z4,z6])],[(0,[z0,z332,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z333,z3,z4,z6]),(0,[z0,z1,z2,z334,z3,z4,z6]),(0,[z18,z0,z2,z3,z19,z4,z6]),(0,[z0,z1,z2,z3,z4,z23,z26]),(0,[z0,z1,z2,z3,z335,z4,z6])],[(1,[z96,z1,z2,z3,z4,z129]),(0,[z0,z1,z2,z3,z4,z6,z336]),(0,[z64,z0,z56,z2,z3,z4,z6]),(0,[z80,z0,z1,z2,z3,z4,z23])],[(0,[z337,z0,z1,z2,z3,z4,z6]),(0,[z58,z0,z1,z2,z206,z4,z6]),(0,[z0,z1,z2,z3,z338,z4,z6]),(0,[z0,z1,z2,z3,z4,z23,z29]),(0,[z0,z1,z2,z3,z4,z339,z6]),(0,[z0,z340,z1,z2,z3,z4,z6]),(0,[z80,z0,z1,z49,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z341,z6])]],
   [[(0,[z0,z8,z2,z3,z4,z6,z29]),(0,[z0,z1,z2,z3,z4,z342,z6]),(0,[z38,z1,z2,z3,z4,z39,z6]),(0,[z64,z0,z1,z241,z3,z4,z6]),(0,[z343,z0,z1,z2,z3,z4,z6]),(0,[z0,z273,z1,z3,z217,z4,z6]),(0,[z0,z1,z2,z3,z4,z344,z6])],[(0,[z345,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z81,z3,z4,z74,z6]),(0,[z0,z1,z2,z286,z3,z4,z6])],[(0,[z0,z1,z2,z81,z3,z4,z6]),(0,[z0,z1,z126,z2,z3,z4,z230]),(0,[z0,z346,z1,z2,z3,z4,z6]),(0,[z38,z0,z1,z2,z3,z46,z6])],[(0,[z21,z96,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z347])],[(0,[z0,z1,z2,z3,z348,z4,z6]),(0,[z188,z1,z2,z3,z46,z4,z6]),(1,[z0,z1,z2,z349,z3,z6]),(0,[z0,z1,z2,z3,z350,z4,z6]),(0,[z0,z1,z2,z3,z4,z26,z69]),(0,[z28,z0,z1,z2,z3,z217,z6]),(0,[z0,z1,z2,z3,z351,z4,z6])],[(0,[z45,z7,z1,z2,z3,z4,z6]),(0,[z0,z1,z352,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z353]),(1,[z0,z314,z1,z2,z3,z4]),(0,[z0,z1,z354,z2,z3,z4,z6]),(0,[z64,z0,z195,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z26,z300,z6]),(0,[z0,z1,z2,z355,z3,z4,z6]),(0,[z0,z1,z2,z356,z3,z4,z6]),(0,[z0,z357,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z34,z6,z358])],[(0,[z0,z1,z2,z359,z3,z4,z6]),(0,[z0,z360,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z361,z6]),(0,[z0,z1,z362,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z363,z4,z6])],[(0,[z0,z1,z364,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z365,z4,z6]),(0,[z0,z366,z1,z2,z3,z4,z6]),(0,[z96,z0,z1,z2,z3,z4,z50]),(0,[z0,z367,z1,z2,z3,z4,z6]),(0,[z368,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z369,z3,z4,z6])]],
   [[(0,[z0,z1,z370,z2,z3,z4,z6]),(0,[z0,z371,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z372])],[(0,[z0,z1,z2,z3,z4,z6,z373]),(0,[z0,z1,z2,z3,z14,z39,z6]),(0,[z374,z0,z1,z2,z3,z4,z6]),(0,[z134,z0,z1,z2,z3,z4,z6])],[(0,[z0,z375,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z376,z6]),(0,[z0,z1,z2,z107,z164,z4,z6]),(0,[z0,z1,z2,z3,z4,z377,z6]),(0,[z0,z1,z378,z2,z3,z4,z6])],[(0,[z379,z0,z1,z2,z3,z4,z6]),(0,[z134,z0,z57,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z164,z4,z6]),(0,[z380,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z381,z4,z6])],[(0,[z382,z0,z1,z2,z3,z4,z6]),(0,[z64,z0,z1,z57,z3,z4,z6]),(0,[z0,z1,z2,z349,z3,z164,z6]),(0,[z0,z79,z1,z2,z84,z3,z6]),(0,[z0,z1,z2,z3,z4,z383,z6])],[(0,[z226,z0,z1,z2,z101,z4,z6]),(0,[z0,z1,z2,z384,z3,z4,z6]),(0,[z0,z68,z1,z2,z3,z4,z69])],[(0,[z0,z1,z385,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z386,z6]),(0,[z0,z273,z1,z126,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z387,z6]),(0,[z0,z1,z2,z388,z3,z4,z6])]],
   [[(0,[z0,z389,z1,z2,z3,z4,z6]),(1,[z0,z390,z1,z2,z3,z6]),(1,[z0,z111,z2,z3,z4,z29]),(0,[z391,z0,z1,z2,z3,z4,z6]),(0,[z28,z0,z1,z2,z24,z4,z6]),(0,[z0,z392,z1,z2,z3,z4,z6])],[(1,[z0,z100,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z393,z6]),(0,[z0,z1,z394,z2,z3,z4,z6])],[(0,[z0,z1,z395,z2,z3,z4,z6]),(0,[z64,z0,z1,z2,z72,z4,z6]),(0,[z0,z1,z396,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z29,z69]),(0,[z0,z1,z159,z2,z3,z4,z6]),(0,[z0,z195,z1,z3,z108,z4,z6])],[(0,[z397,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z139,z4]),(0,[z398,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z399,z6])],[(0,[z0,z1,z2,z3,z4,z6,z400]),(0,[z0,z1,z2,z3,z401,z4,z6]),(0,[z0,z1,z2,z3,z402,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z403]),(0,[z0,z1,z159,z2,z108,z4,z6]),(0,[z0,z1,z2,z404,z3,z4,z6])],[(0,[z0,z1,z405,z2,z3,z4,z6])],[(0,[z21,z0,z1,z2,z181,z4,z6]),(0,[z0,z1,z406,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z407,z4,z6]),(0,[z0,z1,z2,z3,z408,z4,z6]),(0,[z409,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z410,z2,z3,z4,z6])],[(0,[z0,z1,z411,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z412,z6]),(0,[z134,z0,z1,z2,z3,z4,z26])]],
   [[(0,[z0,z7,z2,z3,z4,z6,z29]),(0,[z0,z1,z2,z3,z4,z6,z413]),(0,[z0,z414,z1,z2,z3,z4,z6]),(0,[z415,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z30,z3,z15])],[(0,[z64,z0,z1,z2,z3,z4,z416]),(0,[z134,z0,z1,z2,z3,z4,z29]),(0,[z0,z1,z2,z417,z3,z4,z6]),(0,[z0,z1,z418,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z419,z6])],[(0,[z0,z1,z2,z3,z4,z420,z6]),(0,[z0,z421,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z55,z4,z6]),(1,[z0,z195,z1,z108,z4,z6]),(0,[z0,z1,z2,z3,z422,z4,z6]),(0,[z0,z1,z2,z3,z4,z423,z6])],[(0,[z0,z1,z424,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z425,z4,z6])],[(0,[z0,z1,z2,z3,z426,z4,z6]),(0,[z45,z0,z8,z2,z3,z4,z6]),(0,[z132,z9,z1,z2,z3,z4,z6]),(0,[z9,z0,z1,z81,z3,z4,z6]),(0,[z0,z1,z57,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z324,z4,z6]),(1,[z134,z0,z2,z3,z4,z26]),(1,[z0,z1,z2,z3,z6,z358])],[(0,[z427,z0,z1,z2,z3,z4,z6]),(0,[z0,z428,z1,z2,z3,z4,z6]),(0,[z226,z0,z1,z2,z32,z4,z6]),(0,[z0,z429,z1,z2,z3,z4,z6])],[(0,[z0,z100,z1,z2,z3,z4,z6]),(0,[z21,z0,z1,z2,z3,z204,z6]),(0,[z0,z56,z1,z3,z4,z6,z50]),(1,[z0,z273,z1,z3,z217,z6])],[(0,[z0,z430,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z431]),(0,[z0,z1,z2,z3,z432,z4,z6]),(0,[z0,z1,z2,z3,z217,z4,z6]),(0,[z28,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z433,z4,z6]),(0,[z434,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z435,z4,z6])],[(0,[z436,z0,z1,z2,z3,z4,z6]),(0,[z437,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z438]),(0,[z18,z0,z1,z2,z84,z3,z6]),(0,[z0,z1,z2,z3,z439,z4,z6]),(0,[z0,z1,z440,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z441,z4,z6]),(0,[z0,z1,z2,z3,z442,z4,z6]),(0,[z1,z2,z3,z4,z129,z6,z22]),(0,[z0,z1,z2,z3,z4,z6,z443]),(0,[z0,z1,z2,z30,z3,z4,z15]),(0,[z0,z1,z2,z3,z4,z6,z444])],[(0,[z0,z1,z2,z3,z445,z4,z6]),(0,[z446,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z136,z6]),(0,[z0,z273,z1,z222,z3,z4,z6]),(0,[z28,z0,z1,z2,z4,z6,z69]),(0,[z0,z1,z2,z3,z447,z4,z6]),(0,[z0,z1,z2,z30,z3,z4,z25]),(0,[z0,z1,z448,z2,z3,z4,z6])],[(0,[z0,z1,z2,z449,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z197,z6]),(0,[z0,z450,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z451,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z452,z6]),(1,[z0,z1,z3,z4,z300,z6]),(0,[z453,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z454,z3,z4,z6]),(1,[z0,z1,z2,z274,z4,z6]),(0,[z0,z455,z1,z2,z3,z4,z6])]],
   [[(0,[z456,z0,z1,z2,z3,z4,z6]),(0,[z0,z457,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z34,z50])],[(0,[z9,z0,z1,z2,z3,z151,z6]),(0,[z0,z1,z2,z24,z101,z4,z6]),(0,[z0,z1,z2,z3,z458,z4,z6]),(0,[z0,z1,z2,z3,z4,z459,z6])],[(0,[z460,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z6])],[(0,[z64,z0,z1,z2,z3,z461,z6]),(0,[z0,z56,z1,z107,z3,z4,z6]),(0,[z0,z1,z2,z3,z165,z4,z6]),(0,[z0,z79,z2,z3,z4,z67,z6]),(0,[z0,z1,z2,z462,z3,z4,z6])],[(0,[z58,z0,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z46,z4,z39,z6]),(0,[z0,z1,z463,z2,z3,z4,z6]),(1,[z0,z1,z159,z107,z4,z6]),(0,[z0,z1,z2,z4,z34,z6,z69]),(0,[z0,z1,z2,z3,z464,z4,z6])],[(0,[z465,z0,z1,z2,z3,z4,z6]),(0,[z0,z466,z1,z2,z3,z4,z6])],[(1,[z0,z1,z2,z3,z4,z230]),(1,[z0,z1,z2,z3,z52,z6])],[(1,[z0,z1,z105,z3,z4,z6]),(0,[z64,z0,z2,z241,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z467,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z468,z6])],[(0,[z0,z1,z2,z3,z469,z4,z6]),(0,[z0,z1,z2,z3,z470,z4,z6]),(0,[z0,z195,z1,z2,z107,z4,z6]),(0,[z0,z1,z49,z2,z3,z4,z23])],[(0,[z88,z0,z1,z2,z3,z4,z6])],[(1,[z45,z7,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z471,z6]),(0,[z0,z1,z2,z3,z4,z26,z50])],[(1,[z0,z1,z2,z3,z4,z85]),(1,[z58,z1,z2,z101,z4,z6]),(0,[z96,z0,z1,z2,z3,z4,z22]),(0,[z0,z1,z2,z3,z4,z472,z6]),(0,[z96,z0,z1,z2,z3,z4,z23]),(0,[z96,z0,z1,z2,z24,z3,z4]),(0,[z0,z1,z2,z349,z3,z4,z6]),(0,[z80,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z274,z4,z6]),(0,[z0,z1,z473,z2,z3,z4,z6])],[(0,[z0,z1,z474,z2,z3,z4,z6]),(0,[z475,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z476,z6])]],
   [[(0,[z58,z0,z1,z2,z32,z4,z6]),(0,[z0,z1,z477,z2,z3,z4,z6])],[(0,[z478,z0,z1,z2,z3,z4,z6]),(1,[z9,z1,z81,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z4,z6]),(0,[z0,z1,z2,z3,z479,z4,z6]),(0,[z0,z1,z480,z2,z3,z4,z6]),(0,[z0,z1,z2,z107,z205,z4,z6]),(0,[z0,z1,z481,z2,z3,z4,z6]),(0,[z482,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z483,z6])],[(0,[z188,z0,z1,z2,z3,z4,z6]),(0,[z484,z0,z1,z2,z4,z39,z6]),(0,[z0,z1,z2,z3,z139,z4,z6]),(0,[z485,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z29]),(0,[z0,z1,z2,z30,z3,z4,z6])],[(0,[z486,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z487]),(0,[z0,z1,z2,z488,z3,z4,z6])],[(0,[z0,z1,z489,z2,z3,z4,z6]),(1,[z132,z1,z126,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z490]),(0,[z0,z195,z1,z2,z3,z4,z35]),(0,[z0,z1,z2,z3,z4,z491,z6]),(0,[z0,z1,z492,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z493,z4,z6]),(0,[z96,z0,z1,z2,z3,z14,z4])],[(0,[z0,z1,z2,z494,z3,z4,z6]),(0,[z0,z1,z2,z153,z3,z4,z6]),(0,[z495,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z194,z6])],[(0,[z496,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z153,z3,z101,z4]),(0,[z0,z1,z2,z497,z3,z4,z6]),(0,[z0,z1,z498,z2,z3,z4,z6]),(0,[z499,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z206,z4,z124,z6])]],
   [[(0,[z500,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z501,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z75,z34,z6]),(0,[z0,z502,z1,z2,z3,z4,z6])],[(0,[z135,z0,z2,z3,z164,z4,z6]),(0,[z0,z79,z1,z2,z3,z19,z6]),(0,[z503,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z216,z6]),(0,[z0,z1,z504,z2,z3,z4,z6])],[(0,[z0,z1,z2,z505,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z29,z50])],[(0,[z0,z1,z2,z3,z4,z6,z506]),(0,[z0,z1,z2,z24,z206,z4,z6])],[(0,[z0,z390,z1,z2,z3,z164,z6]),(0,[z0,z1,z507,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z124,z6]),(0,[z0,z508,z1,z2,z3,z4,z6])],[(0,[z0,z1,z509,z2,z3,z4,z6]),(0,[z0,z510,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z511,z6]),(0,[z512,z0,z1,z2,z3,z4,z6])],[(0,[z38,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z14,z25,z6])],[(1,[z0,z1,z2,z3,z151,z6]),(0,[z513,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z514]),(1,[z0,z261,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z515,z4,z6]),(0,[z516,z0,z1,z2,z3,z4,z6]),(0,[z135,z0,z1,z2,z3,z4,z438])]],
   [[(0,[z9,z0,z1,z126,z3,z4,z6]),(0,[z0,z517,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z518,z4,z6]),(1,[z28,z0,z1,z2,z124,z6])],[(0,[z519,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z101,z4,z6]),(0,[z64,z80,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z520,z4,z6]),(0,[z0,z1,z521,z2,z3,z4,z6]),(0,[z0,z1,z2,z522,z3,z4,z6])],[(0,[z0,z1,z2,z3,z523,z4,z6]),(0,[z0,z1,z2,z524,z3,z4,z6])],[(0,[z64,z0,z2,z3,z4,z6,z29]),(0,[z0,z1,z2,z3,z4,z525,z6]),(0,[z0,z1,z222,z2,z3,z74,z6]),(0,[z0,z526,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z527,z3,z4,z6]),(0,[z0,z1,z528,z2,z3,z4,z6]),(1,[z484,z0,z1,z2,z4,z6])],[(0,[z529,z0,z1,z2,z3,z4,z6]),(0,[z0,z193,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z530,z6]),(0,[z0,z531,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z532,z3,z4,z6]),(0,[z0,z533,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z227,z3,z4,z6])],[(0,[z0,z1,z2,z534,z3,z4,z6]),(0,[z0,z1,z126,z2,z3,z4,z291]),(0,[z0,z79,z1,z2,z3,z67,z6]),(0,[z535,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z25,z6,z15])]],
   [[(0,[z536,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z324,z4,z6]),(0,[z537,z0,z1,z2,z3,z4,z6]),(0,[z135,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z538,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z74,z6]),(0,[z0,z1,z2,z3,z4,z6,z539])],[(0,[z0,z195,z56,z1,z3,z4,z6]),(0,[z0,z540,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z4,z25,z6,z271])],[(0,[z0,z1,z2,z3,z541,z4,z6]),(0,[z0,z1,z2,z3,z4,z416,z6]),(1,[z18,z0,z2,z3,z19,z6]),(0,[z0,z1,z2,z3,z4,z6,z542]),(0,[z0,z273,z1,z2,z3,z217,z6]),(0,[z0,z1,z2,z3,z4,z543,z6])],[(1,[z0,z1,z2,z3,z4,z197]),(0,[z0,z544,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z545,z3,z4,z6]),(0,[z0,z1,z2,z3,z546,z4,z6]),(0,[z0,z1,z2,z3,z547,z4,z6]),(0,[z0,z1,z2,z3,z548,z4,z6]),(0,[z0,z1,z2,z549,z3,z4,z6]),(0,[z550,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z551,z6]),(0,[z0,z1,z2,z552,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z553]),(0,[z226,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z554,z2,z3,z4,z6]),(0,[z0,z555,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z84,z206,z6])],[(0,[z0,z1,z126,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z15])],[(0,[z64,z88,z1,z2,z3,z4,z6]),(0,[z556,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z75,z6]),(0,[z0,z1,z2,z30,z3,z6,z15])],[(0,[z132,z1,z126,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z557]),(0,[z0,z558,z1,z2,z3,z4,z6])]],
   [[(0,[z20,z0,z8,z2,z3,z4,z6]),(0,[z0,z1,z159,z107,z3,z4,z6]),(0,[z559,z0,z1,z2,z3,z4,z6])],[(0,[z0,z560,z1,z2,z3,z4,z6]),(0,[z561,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z562,z6]),(0,[z0,z1,z2,z563,z3,z4,z6])],[(0,[z564,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z23,z69]),(0,[z0,z1,z2,z3,z565,z4,z6])],[(0,[z0,z566,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z567,z4,z6])],[(0,[z0,z1,z2,z3,z4,z568,z6]),(0,[z0,z1,z126,z3,z4,z74,z6]),(1,[z0,z1,z2,z3,z86,z6]),(0,[z0,z1,z2,z3,z204,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z114]),(0,[z0,z1,z2,z569,z3,z4,z6]),(0,[z0,z1,z2,z3,z570,z4,z6]),(0,[z0,z1,z2,z571,z4,z25,z6])],[(0,[z0,z1,z1,z2,z3,z4,z6]),(0,[z0,z1,z572,z2,z3,z4,z6]),(0,[z64,z0,z1,z2,z3,z4,z114]),(0,[z573,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z574,z4,z6]),(0,[z0,z1,z575,z2,z3,z4,z6])],[(0,[z576,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z32,z4,z6,z69]),(0,[z0,z1,z2,z3,z4,z6,z577]),(0,[z0,z1,z2,z3,z461,z4,z6]),(0,[z578,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z579,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z580,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z581]),(0,[z0,z1,z2,z582,z3,z4,z6]),(0,[z0,z1,z2,z571,z3,z4,z6])],[(0,[z0,z1,z2,z3,z583,z4,z6])],[(0,[z0,z1,z584,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z585,z6])],[(1,[z0,z1,z3,z165,z4,z6]),(0,[z0,z1,z2,z3,z206,z4,z6]),(0,[z0,z1,z2,z3,z4,z586,z6])],[(0,[z0,z1,z2,z3,z4,z6,z587]),(0,[z0,z588,z1,z2,z3,z4,z6]),(0,[z0,z589,z1,z2,z3,z4,z6])],[],[(0,[z590,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z591,z6])],[(0,[z0,z592,z1,z2,z3,z4,z6]),(0,[z0,z195,z1,z2,z3,z4,z431])]],
   [[(0,[z593,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z594,z6]),(1,[z0,z1,z2,z72,z4,z6]),(0,[z595,z0,z1,z2,z3,z4,z6]),(1,[z80,z0,z1,z3,z4,z23])],[(0,[z0,z1,z2,z596,z3,z4,z6]),(0,[z0,z163,z1,z2,z205,z4,z6]),(0,[z0,z1,z49,z2,z3,z4,z6])],[(0,[z0,z1,z597,z2,z3,z4,z6]),(0,[z598,z0,z1,z2,z3,z4,z6]),(0,[z21,z0,z1,z2,z55,z4,z6]),(0,[z0,z1,z2,z599,z3,z4,z6])],[(0,[z0,z1,z2,z164,z108,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z143]),(1,[z0,z1,z2,z571,z4,z6])],[(0,[z0,z1,z600,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z14,z46,z6]),(0,[z21,z0,z1,z2,z3,z4,z50]),(0,[z0,z1,z2,z3,z4,z601,z6])],[(0,[z0,z1,z2,z3,z4,z602,z6]),(1,[z64,z0,z241,z3,z4,z6]),(0,[z0,z390,z1,z2,z3,z4,z6]),(0,[z0,z273,z1,z2,z3,z4,z6]),(0,[z603,z0,z1,z2,z3,z4,z6]),(0,[z28,z0,z1,z2,z3,z124,z6]),(0,[z0,z1,z2,z3,z604,z4,z6]),(0,[z0,z1,z2,z24,z4,z34,z6])],[(1,[z0,z1,z2,z497,z3,z4]),(0,[z64,z0,z1,z2,z3,z4,z6])],[(0,[z38,z0,z1,z77,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z416]),(0,[z0,z1,z2,z3,z4,z605,z6]),(0,[z0,z1,z2,z606,z3,z4,z6])]],
   [[(0,[z20,z0,z7,z2,z3,z4,z6]),(0,[z0,z1,z607,z2,z3,z4,z6]),(0,[z0,z1,z2,z608,z3,z4,z6]),(0,[z0,z1,z2,z24,z3,z4,z6])],[(0,[z28,z38,z0,z1,z2,z3,z6]),(0,[z64,z0,z1,z107,z3,z4,z6]),(0,[z0,z1,z2,z3,z67,z74,z6])],[(0,[z0,z1,z2,z3,z4,z609,z6]),(0,[z0,z1,z2,z3,z4,z610,z6]),(0,[z0,z1,z2,z77,z3,z4,z6]),(0,[z0,z1,z2,z611,z3,z4,z6])],[(0,[z96,z1,z2,z3,z4,z129,z6]),(0,[z64,z0,z1,z2,z3,z194,z6]),(1,[z0,z79,z2,z3,z67,z6]),(0,[z446,z0,z1,z3,z4,z26,z6])],[(0,[z612,z0,z1,z2,z3,z4,z6]),(0,[z613,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z614,z3,z4,z6])],[(0,[z615,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z205,z3,z4,z6]),(0,[z616,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z81,z3,z4,z6,z50]),(0,[z0,z1,z2,z3,z617,z4,z6]),(0,[z0,z1,z2,z101,z4,z6,z69]),(0,[z0,z1,z2,z3,z618,z4,z6]),(0,[z0,z1,z2,z3,z4,z619,z6])],[(0,[z0,z1,z620,z2,z3,z4,z6]),(0,[z45,z0,z7,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z621,z6]),(0,[z0,z56,z1,z241,z3,z4,z6]),(0,[z0,z1,z2,z205,z108,z4,z6]),(0,[z0,z622,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z623,z6]),(0,[z0,z1,z2,z3,z624,z4,z6]),(0,[z0,z1,z2,z3,z625,z4,z6])]],
   [[(1,[z20,z8,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z217,z39,z6]),(1,[z0,z1,z2,z3,z4,z438]),(0,[z626,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z627,z4,z6]),(1,[z0,z193,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z628,z6]),(0,[z0,z79,z1,z2,z3,z4,z6]),(0,[z0,z1,z629,z2,z3,z4,z6]),(0,[z0,z1,z2,z630,z3,z4,z6]),(0,[z28,z0,z1,z2,z3,z74,z6]),(0,[z631,z0,z1,z2,z3,z4,z6]),(0,[z0,z632,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z633]),(0,[z0,z1,z2,z3,z4,z634,z6]),(0,[z0,z1,z2,z3,z4,z6,z635])],[(1,[z0,z1,z2,z3,z4,z291]),(0,[z0,z636,z1,z2,z3,z4,z6]),(0,[z484,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z497,z3,z4,z39]),(0,[z0,z1,z2,z637,z3,z4,z6])],[(0,[z132,z0,z1,z126,z3,z4,z6]),(0,[z0,z1,z2,z24,z32,z4,z6]),(0,[z96,z0,z1,z2,z3,z4,z29]),(0,[z0,z1,z2,z638,z3,z4,z6]),(0,[z0,z1,z2,z639,z3,z4,z6]),(1,[z446,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z640,z6])],[(0,[z0,z1,z2,z3,z641,z4,z6]),(0,[z0,z1,z2,z642,z3,z4,z6]),(0,[z0,z1,z2,z3,z643,z4,z6]),(0,[z0,z2,z3,z4,z23,z303,z6]),(0,[z0,z1,z2,z24,z3,z4,z34])],[(0,[z0,z644,z1,z2,z3,z4,z6]),(0,[z645,z0,z1,z2,z3,z4,z6]),(0,[z28,z0,z1,z2,z3,z6,z15]),(0,[z0,z1,z2,z84,z206,z4,z6])],[(0,[z0,z1,z2,z3,z646,z4,z6]),(0,[z0,z1,z2,z3,z647,z4,z6]),(0,[z648,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z24,z4,z34])]],
   [[(0,[z649,z0,z1,z2,z3,z4,z6]),(0,[z0,z158,z1,z3,z164,z4,z6]),(0,[z0,z1,z2,z3,z650,z4,z6]),(0,[z0,z651,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z652,z3,z4,z6])],[(1,[z0,z1,z2,z3,z461,z6]),(0,[z0,z1,z2,z3,z653,z4,z6]),(0,[z28,z0,z1,z2,z3,z14,z6]),(0,[z0,z1,z2,z3,z4,z654,z6])],[(0,[z0,z1,z2,z3,z4,z655,z6]),(0,[z0,z1,z2,z656,z3,z4,z6]),(0,[z0,z657,z1,z2,z3,z4,z6]),(1,[z0,z68,z1,z2,z4,z69])],[(0,[z134,z0,z8,z2,z3,z4,z6]),(0,[z0,z1,z658,z2,z3,z4,z6]),(0,[z0,z56,z1,z57,z3,z4,z6]),(1,[z0,z158,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z431,z6])],[(0,[z659,z0,z1,z2,z3,z4,z6]),(1,[z188,z1,z2,z3,z46,z6]),(0,[z660,z0,z1,z2,z3,z4,z6]),(0,[z0,z273,z1,z2,z3,z74,z6]),(0,[z0,z1,z2,z3,z4,z6,z661])],[(0,[z0,z1,z2,z3,z662,z4,z6]),(0,[z0,z1,z663,z2,z3,z4,z6]),(0,[z0,z195,z1,z159,z3,z4,z6]),(0,[z0,z1,z2,z3,z664,z4,z6]),(0,[z28,z0,z1,z2,z3,z206,z6])],[(0,[z0,z665,z1,z2,z3,z4,z6]),(1,[z0,z1,z227,z3,z4,z6]),(0,[z666,z0,z1,z2,z3,z4,z6])],[(1,[z0,z1,z231,z3,z4,z6]),(0,[z0,z667,z1,z2,z3,z4,z6]),(0,[z0,z1,z668,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z669]),(0,[z0,z670,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z303,z6])]],
   [[(0,[z671,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z672,z4,z6]),(0,[z0,z1,z2,z3,z673,z4,z6]),(0,[z0,z1,z2,z674,z3,z4,z6]),(0,[z134,z0,z111,z2,z3,z4,z6])],[(0,[z0,z1,z2,z675,z3,z4,z6]),(0,[z0,z676,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z19,z4,z6]),(0,[z0,z1,z2,z677,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z678,z6])],[(0,[z96,z0,z1,z2,z30,z3,z4]),(0,[z0,z1,z2,z3,z4,z679,z6]),(0,[z0,z1,z2,z3,z680,z4,z6])],[(0,[z64,z263,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z681,z6]),(0,[z682,z0,z1,z2,z3,z4,z6])],[(0,[z58,z226,z1,z2,z3,z4,z6]),(0,[z683,z0,z1,z2,z3,z4,z6]),(0,[z28,z0,z1,z2,z84,z4,z6]),(0,[z684,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z25,z6])],[(0,[z0,z1,z2,z3,z685,z4,z6]),(0,[z80,z0,z1,z2,z3,z4,z50]),(0,[z0,z1,z2,z3,z4,z34,z6])],[(0,[z0,z1,z126,z3,z4,z6,z50]),(0,[z0,z57,z2,z241,z3,z4,z6]),(0,[z686,z0,z1,z2,z3,z4,z6]),(0,[z687,z0,z1,z2,z3,z4,z6]),(0,[z0,z688,z1,z2,z3,z4,z6]),(0,[z0,z1,z689,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z690,z4,z6]),(0,[z0,z1,z691,z2,z3,z4,z6]),(0,[z0,z1,z2,z107,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z3,z4,z6]),(0,[z0,z1,z2,z84,z3,z217,z6]),(0,[z0,z1,z2,z206,z4,z6,z69])],[(0,[z0,z1,z2,z3,z4,z692,z6]),(0,[z0,z1,z2,z3,z4,z6,z358]),(0,[z0,z1,z2,z3,z4,z693,z6])],[(0,[z1,z2,z32,z3,z101,z4,z6]),(0,[z0,z1,z2,z3,z4,z39,z6]),(0,[z0,z1,z2,z3,z4,z694,z6]),(0,[z0,z1,z2,z3,z108,z4,z6])],[(0,[z132,z0,z1,z81,z3,z4,z6]),(0,[z0,z1,z2,z286,z3,z101,z6]),(0,[z188,z0,z1,z2,z3,z39,z6]),(0,[z0,z1,z2,z3,z4,z6,z695]),(0,[z0,z68,z1,z2,z24,z4,z6]),(0,[z696,z0,z1,z2,z3,z4,z6])],[],[(0,[z0,z1,z2,z697,z3,z4,z6]),(0,[z0,z698,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z69])],[(0,[z699,z0,z1,z2,z3,z4,z6]),(0,[z0,z79,z1,z2,z3,z4,z266]),(0,[z0,z700,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z701,z6]),(0,[z702,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z703,z6]),(0,[z21,z0,z261,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z704,z6]),(0,[z0,z705,z1,z2,z3,z4,z6]),(0,[z0,z1,z706,z2,z3,z4,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z707,z1,z2,z3,z4,z6]),(0,[z0,z79,z2,z3,z67,z143]),(0,[z0,z1,z2,z3,z708,z6])],[(0,[z0,z1,z2,z3,z4,z709]),(0,[z0,z1,z2,z3,z710,z6]),(0,[z484,z0,z1,z2,z497,z4]),(0,[z64,z0,z241,z3,z194,z6]),(0,[z0,z1,z2,z3,z4,z711])],[(0,[z0,z1,z2,z3,z10,z6]),(0,[z96,z0,z1,z3,z4,z300]),(0,[z135,z0,z2,z164,z4,z438]),(0,[z0,z712,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z713,z6]),(0,[z0,z1,z2,z3,z344,z15])],[(0,[z436,z28,z0,z1,z2,z6]),(0,[z0,z1,z2,z3,z194,z416])],[(0,[z0,z1,z2,z3,z4,z714]),(0,[z0,z1,z3,z715,z4,z6]),(0,[z134,z446,z0,z3,z4,z6])],[(0,[z0,z1,z2,z3,z716,z6]),(0,[z0,z1,z3,z717,z4,z6]),(0,[z0,z1,z2,z718,z4,z6]),(0,[z0,z1,z2,z719,z4,z6])],[(0,[z0,z1,z222,z3,z720,z6])],[(0,[z0,z1,z2,z3,z4,z438])]],
   [[(0,[z0,z193,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z721])],[(0,[z0,z1,z2,z3,z4,z291]),(0,[z226,z1,z2,z604,z4,z6]),(0,[z0,z193,z2,z181,z4,z6]),(0,[z722,z0,z2,z3,z4,z6])],[(0,[z28,z0,z1,z2,z618,z6]),(0,[z21,z1,z2,z3,z4,z471]),(0,[z0,z56,z1,z3,z4,z35]),(0,[z135,z0,z2,z164,z4,z6]),(0,[z0,z1,z2,z84,z6,z661])],[(0,[z0,z2,z3,z4,z723,z6]),(0,[z0,z1,z2,z3,z720,z6]),(0,[z80,z0,z1,z3,z4,z724]),(0,[z725,z0,z1,z3,z4,z6])],[(0,[z631,z0,z2,z3,z19,z6])],[(0,[z0,z1,z726,z3,z4,z6]),(0,[z727,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z728,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z729,z2,z3,z4]),(0,[z0,z1,z717,z108,z4,z6])],[(0,[z0,z1,z2,z3,z6,z730]),(0,[z0,z1,z2,z731,z4,z6]),(0,[z732,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z181,z4,z6]),(0,[z0,z193,z2,z3,z204,z6]),(0,[z0,z158,z1,z3,z4,z6]),(0,[z134,z446,z0,z3,z4,z26])],[(0,[z0,z1,z2,z3,z4,z733]),(0,[z0,z1,z2,z3,z4,z734]),(0,[z188,z1,z2,z3,z46,z6])],[(0,[z0,z1,z2,z735,z3,z4]),(0,[z21,z1,z2,z3,z86,z22]),(0,[z263,z1,z2,z72,z4,z6]),(0,[z0,z158,z1,z108,z4,z6])],[(0,[z0,z1,z2,z3,z736,z6]),(0,[z0,z1,z227,z3,z4,z6]),(0,[z28,z0,z1,z2,z177,z6]),(0,[z0,z2,z3,z4,z416,z29]),(0,[z28,z578,z0,z1,z2,z6])],[(0,[z0,z1,z2,z3,z737,z6]),(0,[z0,z193,z2,z3,z4,z26]),(0,[z0,z1,z2,z3,z6,z738]),(0,[z0,z1,z2,z571,z6,z15])],[(0,[z0,z1,z227,z181,z4,z6]),(0,[z0,z1,z2,z3,z4,z739])]],
   [[(0,[z740,z0,z2,z3,z4,z291]),(0,[z0,z1,z2,z741,z3,z6]),(1,[z0,z2,z3,z4,z723])],[(0,[z0,z1,z742,z3,z4,z6]),(0,[z0,z2,z3,z4,z743,z6])],[(0,[z0,z1,z2,z3,z4,z744]),(0,[z0,z1,z2,z3,z26,z358]),(0,[z0,z1,z745,z3,z4,z6])],[(0,[z0,z1,z2,z746,z4,z6]),(0,[z0,z2,z3,z4,z747,z6]),(0,[z263,z1,z2,z3,z4,z416]),(0,[z0,z1,z2,z3,z748,z6])],[(0,[z749,z1,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z723,z29]),(0,[z0,z195,z1,z108,z4,z35])],[(0,[z0,z2,z3,z19,z750,z6])],[(0,[z740,z0,z2,z3,z4,z6])],[(0,[z0,z1,z227,z3,z204,z6]),(0,[z0,z1,z2,z3,z4,z751])]],
   [[(0,[z0,z1,z2,z3,z752,z6]),(0,[z188,z484,z0,z1,z2,z6]),(0,[z0,z1,z231,z3,z204,z6]),(0,[z0,z1,z2,z181,z4,z26]),(0,[z64,z0,z3,z4,z29,z50]),(0,[z446,z0,z1,z3,z4,z50])],[(0,[z0,z1,z2,z753,z4,z6]),(0,[z0,z1,z2,z754,z3,z6]),(0,[z0,z1,z222,z3,z74,z6])],[(0,[z0,z112,z2,z3,z4,z29]),(0,[z0,z1,z2,z181,z4,z29]),(0,[z0,z1,z3,z720,z4,z6])],[(0,[z0,z1,z227,z3,z4,z26])],[(0,[z0,z1,z2,z3,z4,z755])],[(0,[z0,z1,z756,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z757]),(0,[z0,z1,z2,z758,z4,z6]),(0,[z0,z1,z759,z3,z4,z6]),(0,[z0,z1,z2,z3,z760,z6]),(0,[z200,z0,z2,z3,z4,z416]),(0,[z0,z1,z159,z107,z52,z6])],[(0,[z0,z1,z2,z3,z4,z761]),(0,[z0,z1,z2,z4,z6,z762]),(0,[z0,z1,z2,z3,z763,z6]),(0,[z0,z1,z2,z3,z4,z764])],[(0,[z0,z1,z3,z4,z765,z6]),(0,[z0,z314,z1,z2,z4,z69]),(0,[z0,z1,z2,z84,z650,z6])]],
   [[(0,[z0,z1,z766,z3,z4,z6])],[(0,[z767,z1,z2,z3,z4,z6])],[(0,[z484,z0,z1,z2,z139,z4]),(0,[z88,z1,z2,z3,z4,z114]),(0,[z0,z768,z2,z3,z4,z6])],[(0,[z0,z1,z769,z3,z4,z6]),(0,[z0,z1,z231,z3,z4,z50]),(0,[z96,z1,z2,z652,z3,z4])],[(0,[z134,z0,z2,z3,z4,z197]),(0,[z0,z261,z2,z55,z4,z6])],[(0,[z263,z1,z2,z3,z4,z6]),(0,[z0,z1,z580,z3,z74,z6]),(0,[z0,z1,z2,z3,z4,z266])],[(0,[z0,z1,z2,z3,z770,z6]),(0,[z0,z261,z2,z3,z4,z50]),(0,[z0,z1,z2,z4,z6,z271])],[(0,[z771,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z772,z4,z6])]],
   [[(0,[z0,z1,z2,z773,z4,z6]),(0,[z626,z0,z2,z3,z4,z26])],[(0,[z0,z774,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z775]),(0,[z0,z1,z2,z776,z3,z6]),(1,[z0,z1,z3,z720,z6]),(0,[z0,z1,z584,z3,z217,z6]),(0,[z0,z1,z2,z3,z4,z724])],[(0,[z226,z0,z100,z1,z2,z6]),(0,[z0,z421,z1,z3,z217,z6])],[(0,[z0,z1,z2,z497,z3,z15]),(0,[z1,z2,z3,z4,z6,z777]),(0,[z0,z195,z1,z324,z4,z6])],[(0,[z45,z7,z2,z3,z4,z85]),(0,[z0,z1,z778,z3,z4,z6]),(0,[z0,z1,z2,z779,z4,z6])],[(0,[z0,z1,z2,z3,z4,z780]),(0,[z0,z1,z126,z3,z151,z6]),(0,[z0,z781,z2,z3,z4,z6]),(0,[z132,z1,z126,z3,z4,z230]),(0,[z318,z1,z126,z3,z4,z6]),(0,[z0,z782,z2,z3,z4,z6]),(0,[z0,z1,z2,z783,z4,z6])],[(0,[z64,z0,z440,z3,z4,z6]),(0,[z0,z1,z2,z24,z4,z784])],[(0,[z0,z1,z2,z3,z4,z785]),(0,[z0,z1,z259,z3,z4,z50]),(0,[z200,z0,z2,z3,z4,z6])]],
   [[(0,[z135,z0,z390,z2,z164,z6]),(0,[z0,z1,z159,z107,z216,z6])],[(0,[z0,z1,z2,z3,z786,z6]),(0,[z0,z1,z77,z3,z4,z6]),(0,[z226,z1,z2,z32,z4,z6]),(0,[z0,z502,z2,z3,z4,z26]),(0,[z0,z1,z2,z3,z787,z6])],[(0,[z0,z1,z2,z788,z3,z6]),(0,[z38,z1,z2,z3,z39,z6]),(0,[z0,z1,z2,z4,z6,z789]),(0,[z96,z0,z2,z3,z4,z303]),(0,[z0,z2,z3,z4,z303,z6]),(0,[z0,z390,z1,z3,z165,z6]),(0,[z0,z1,z2,z3,z4,z790])],[(0,[z0,z1,z2,z3,z4,z791]),(0,[z0,z1,z792,z3,z4,z6]),(0,[z793,z1,z2,z3,z4,z6])],[(0,[z58,z533,z1,z2,z4,z6])],[(0,[z794,z1,z2,z3,z4,z6])],[(0,[z795,z0,z1,z3,z4,z197]),(0,[z1,z766,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z796])],[(0,[z0,z1,z2,z3,z4,z797]),(0,[z0,z1,z2,z4,z6,z798]),(0,[z21,z1,z231,z3,z4,z22]),(0,[z0,z1,z2,z3,z4,z799])]],
   [[(0,[z0,z1,z2,z3,z800,z6]),(0,[z88,z1,z2,z3,z194,z6]),(0,[z0,z1,z801,z3,z4,z6]),(0,[z1,z2,z3,z4,z6,z802])],[(0,[z0,z1,z2,z3,z4,z803]),(0,[z132,z1,z766,z3,z4,z6]),(0,[z0,z1,z2,z55,z86,z6])],[(0,[z0,z1,z2,z3,z4,z114]),(0,[z0,z1,z2,z4,z34,z784])],[(0,[z368,z0,z2,z164,z4,z6])],[(0,[z0,z1,z2,z804,z4,z6])],[(1,[z1,z2,z3,z760,z6]),(0,[z0,z1,z2,z805,z3,z6]),(0,[z0,z1,z107,z647,z4,z6]),(0,[z200,z0,z2,z3,z4,z26]),(0,[z0,z1,z2,z3,z4,z784])],[(0,[z0,z2,z3,z4,z806,z6])],[(0,[z0,z1,z87,z3,z4,z50]),(0,[z0,z1,z2,z3,z194,z114]),(0,[z200,z0,z2,z3,z4,z29]),(0,[z0,z195,z1,z108,z4,z431]),(0,[z0,z2,z3,z4,z303,z34])]],
   [[(1,[z1,z766,z3,z4,z6]),(0,[z134,z0,z2,z3,z4,z416]),(0,[z0,z1,z3,z4,z724,z50])],[(0,[z0,z1,z2,z3,z807,z6]),(0,[z0,z158,z390,z1,z3,z6]),(0,[z0,z808,z1,z3,z4,z6])],[(0,[z0,z1,z364,z3,z74,z6]),(0,[z96,z1,z2,z3,z4,z129])],[(0,[z9,z1,z81,z3,z151,z6])],[(0,[z0,z1,z81,z3,z151,z6]),(0,[z0,z1,z2,z3,z809,z6]),(0,[z0,z1,z2,z3,z4,z810]),(0,[z1,z2,z3,z4,z6,z811]),(0,[z812,z0,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z813]),(0,[z0,z1,z814,z2,z3,z6]),(0,[z0,z1,z2,z153,z3,z4]),(0,[z0,z815,z1,z2,z4,z6]),(0,[z263,z2,z3,z4,z6,z29]),(0,[z0,z1,z2,z816,z4,z6]),(0,[z0,z1,z2,z84,z523,z6])],[(0,[z0,z1,z2,z3,z817,z6])],[(0,[z0,z1,z2,z3,z4,z818]),(0,[z0,z1,z2,z3,z819,z6]),(0,[z820,z1,z2,z3,z4,z6])]],
   [[],[(0,[z0,z1,z3,z4,z821,z6]),(0,[z0,z1,z2,z3,z4,z822]),(0,[z0,z314,z1,z2,z3,z4]),(0,[z0,z823,z2,z3,z4,z6]),(0,[z21,z392,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z824,z6]),(0,[z0,z1,z2,z3,z4,z143]),(0,[z0,z1,z2,z3,z4,z825])],[(0,[z45,z7,z2,z3,z4,z197]),(0,[z0,z1,z2,z3,z4,z826]),(0,[z0,z827,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z828])],[(0,[z0,z1,z2,z3,z4,z829]),(0,[z0,z1,z3,z4,z830,z6])],[(0,[z0,z1,z2,z3,z4,z831]),(0,[z0,z1,z832,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z833]),(0,[z834,z1,z2,z3,z4,z6]),(0,[z28,z0,z1,z2,z172,z6]),(0,[z0,z1,z2,z206,z835,z6])],[(0,[z0,z195,z1,z717,z4,z6])],[(0,[z0,z1,z836,z3,z4,z6]),(0,[z0,z68,z1,z2,z181,z4]),(0,[z0,z1,z349,z3,z165,z6]),(1,[z0,z1,z3,z4,z724]),(0,[z200,z80,z0,z3,z4,z23])],[(0,[z1,z2,z32,z837,z4,z6]),(0,[z0,z1,z838,z3,z4,z6]),(0,[z64,z263,z241,z3,z4,z6])]],
   [[(0,[z0,z839,z2,z3,z4,z6]),(0,[z38,z1,z2,z497,z3,z39]),(0,[z0,z1,z2,z3,z194,z6]),(0,[z0,z1,z2,z840,z4,z6])],[(0,[z0,z1,z2,z324,z461,z6]),(0,[z0,z1,z2,z3,z4,z841]),(0,[z0,z2,z3,z4,z842,z6])],[(0,[z0,z1,z2,z3,z4,z843]),(0,[z0,z1,z2,z3,z4,z844])],[(0,[z0,z1,z845,z3,z4,z6]),(0,[z0,z1,z2,z846,z4,z6]),(0,[z409,z1,z2,z3,z46,z6]),(0,[z0,z1,z2,z835,z124,z6])],[(0,[z0,z1,z2,z847,z3,z6]),(0,[z0,z1,z2,z3,z848,z6]),(0,[z0,z1,z2,z139,z274,z4]),(0,[z0,z261,z2,z3,z4,z23]),(0,[z0,z390,z1,z2,z3,z6]),(0,[z0,z111,z2,z3,z4,z29]),(0,[z0,z1,z2,z571,z14,z6])],[(0,[z0,z1,z2,z3,z849,z6]),(0,[z0,z100,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z204,z6]),(0,[z0,z163,z2,z205,z4,z6])],[(0,[z0,z850,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z851]),(0,[z0,z193,z2,z55,z4,z6])],[(0,[z0,z852,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z853]),(0,[z0,z1,z2,z3,z6,z854]),(0,[z0,z1,z2,z181,z204,z6]),(0,[z263,z1,z2,z3,z4,z114]),(0,[z0,z1,z2,z855,z4,z6])]],
   [[(0,[z275,z1,z126,z3,z4,z6]),(0,[z0,z1,z856,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z857])],[(0,[z0,z1,z2,z858,z4,z6])],[(0,[z96,z1,z2,z3,z285,z4]),(1,[z0,z2,z783,z4,z6]),(0,[z0,z340,z2,z205,z4,z6])],[(0,[z859,z0,z1,z2,z3,z6]),(0,[z38,z1,z77,z3,z39,z6]),(0,[z0,z1,z2,z3,z860,z6])],[(0,[z0,z1,z861,z3,z4,z6]),(0,[z0,z862,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z863]),(0,[z0,z864,z1,z2,z3,z6]),(0,[z0,z1,z865,z3,z4,z6]),(0,[z0,z1,z2,z3,z866,z6])],[(0,[z0,z1,z2,z4,z6,z867])],[(0,[z0,z1,z2,z3,z4,z868]),(0,[z0,z1,z2,z55,z4,z6])],[(0,[z0,z1,z2,z3,z6,z869]),(0,[z0,z870,z1,z2,z3,z4])]],
   [[(0,[z0,z871,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z6,z358])],[(0,[z0,z1,z2,z3,z4,z872]),(0,[z0,z1,z873,z3,z4,z6]),(0,[z28,z0,z1,z2,z419,z6])],[(0,[z0,z1,z2,z3,z874,z6]),(0,[z0,z1,z2,z875,z3,z6]),(0,[z9,z1,z766,z3,z4,z6]),(0,[z0,z1,z2,z181,z4,z50]),(0,[z0,z111,z2,z3,z4,z723]),(0,[z0,z273,z1,z3,z217,z6]),(0,[z28,z0,z1,z2,z423,z6])],[(0,[z0,z1,z3,z4,z197,z765]),(0,[z0,z1,z227,z55,z4,z6])],[(0,[z0,z314,z1,z2,z181,z4]),(0,[z188,z1,z2,z3,z760,z6]),(0,[z0,z1,z231,z55,z4,z6])],[(0,[z0,z1,z2,z3,z4,z876])],[(0,[z0,z1,z2,z3,z4,z877]),(0,[z0,z261,z2,z3,z86,z6])],[(0,[z1,z2,z837,z101,z4,z6]),(0,[z878,z1,z2,z3,z4,z6]),(0,[z0,z2,z801,z3,z4,z6]),(0,[z0,z1,z2,z3,z738,z15])]],
   [[(0,[z852,z8,z2,z3,z4,z6]),(0,[z0,z1,z879,z2,z3,z6]),(0,[z0,z1,z2,z84,z62,z6])],[(0,[z58,z1,z2,z153,z101,z4]),(0,[z0,z1,z880,z3,z4,z6]),(0,[z0,z1,z3,z4,z416,z50]),(0,[z0,z1,z2,z3,z4,z881])],[(0,[z0,z1,z2,z4,z6,z882])],[(0,[z0,z100,z314,z1,z2,z3]),(0,[z21,z0,z1,z3,z4,z300]),(0,[z135,z0,z2,z164,z4,z136])],[(0,[z0,z1,z2,z3,z4,z883]),(0,[z21,z193,z2,z3,z4,z22]),(0,[z18,z0,z2,z3,z750,z6])],[(0,[z0,z1,z2,z3,z884,z6]),(0,[z58,z314,z1,z2,z101,z4]),(0,[z263,z1,z2,z3,z194,z6]),(0,[z0,z1,z49,z3,z4,z50]),(0,[z28,z0,z1,z2,z6,z270])],[(0,[z0,z1,z2,z286,z3,z6]),(0,[z1,z2,z3,z760,z4,z6]),(0,[z21,z1,z2,z3,z4,z321]),(0,[z0,z1,z2,z3,z4,z885]),(0,[z0,z2,z3,z750,z67,z6])],[(0,[z886,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z887]),(0,[z0,z273,z1,z3,z617,z6]),(0,[z0,z1,z2,z3,z4,z888]),(0,[z0,z1,z2,z3,z4,z889]),(0,[z0,z1,z2,z3,z4,z136]),(0,[z0,z531,z2,z3,z4,z29]),(0,[z134,z0,z2,z3,z4,z723]),(0,[z0,z890,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z891]),(0,[z0,z1,z2,z3,z6,z892]),(0,[z0,z1,z2,z3,z14,z86]),(0,[z0,z1,z2,z3,z893,z6])],[(0,[z0,z1,z2,z3,z4,z894]),(0,[z0,z1,z2,z895,z4,z6]),(0,[z0,z1,z2,z896,z4,z6]),(0,[z0,z1,z159,z717,z4,z6])],[(0,[z0,z1,z2,z897,z4,z6]),(0,[z0,z1,z898,z3,z4,z6]),(0,[z0,z1,z105,z3,z4,z6]),(0,[z183,z1,z81,z3,z4,z6]),(0,[z38,z533,z1,z2,z3,z6]),(0,[z64,z0,z691,z3,z4,z6])],[(0,[z0,z1,z2,z899,z3,z4]),(0,[z21,z1,z2,z3,z4,z22]),(0,[z0,z2,z783,z164,z4,z6]),(0,[z0,z1,z2,z3,z900,z6]),(0,[z0,z1,z3,z720,z74,z6])],[(0,[z0,z1,z2,z3,z4,z901]),(0,[z484,z0,z1,z2,z217,z6]),(0,[z696,z1,z2,z3,z39,z6]),(0,[z0,z1,z2,z902,z4,z6]),(0,[z0,z79,z418,z2,z3,z6])],[(0,[z21,z1,z2,z181,z4,z22]),(0,[z0,z1,z3,z4,z903,z6]),(0,[z0,z904,z2,z3,z4,z6])],[(1,[z852,z2,z3,z4,z6]),(0,[z7,z852,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z905]),(0,[z0,z1,z2,z3,z4,z906]),(0,[z0,z199,z2,z3,z4,z29]),(0,[z0,z1,z3,z4,z300,z34])]],
   [[(0,[z45,z7,z2,z3,z4,z6]),(0,[z0,z1,z2,z4,z784,z69])],[(0,[z0,z1,z2,z3,z4,z85]),(0,[z0,z1,z2,z3,z907,z6]),(0,[z58,z1,z2,z101,z4,z6]),(0,[z58,z100,z1,z2,z101,z6]),(0,[z0,z908,z2,z3,z4,z6]),(0,[z21,z1,z227,z3,z4,z22]),(0,[z64,z0,z3,z4,z6,z581]),(0,[z0,z1,z2,z3,z835,z6])],[(0,[z132,z1,z126,z3,z4,z291])],[(0,[z0,z1,z2,z3,z4,z909]),(0,[z0,z1,z2,z3,z4,z35])],[(0,[z0,z910,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z911,z6]),(0,[z0,z1,z2,z3,z4,z912]),(0,[z21,z1,z2,z3,z4,z777]),(0,[z88,z1,z2,z324,z4,z6]),(0,[z0,z1,z2,z3,z913,z6]),(0,[z80,z0,z3,z4,z23,z303])],[(0,[z0,z1,z2,z3,z914,z6]),(0,[z0,z1,z2,z915,z4,z6]),(0,[z0,z916,z1,z2,z4,z6]),(0,[z0,z1,z2,z75,z6,z69])],[(0,[z21,z1,z2,z3,z204,z22]),(0,[z917,z0,z1,z2,z3,z4])],[(0,[z918,z0,z1,z3,z4,z6]),(0,[z0,z79,z2,z3,z750,z6])]],
   [[(0,[z919,z0,z1,z2,z3,z6]),(0,[z0,z1,z920,z3,z4,z6]),(0,[z132,z1,z126,z3,z4,z6]),(0,[z0,z921,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z922,z6]),(0,[z64,z0,z241,z324,z4,z6])],[(0,[z0,z2,z3,z923,z4,z6]),(0,[z0,z1,z77,z84,z3,z6]),(0,[z80,z263,z1,z3,z4,z6])],[(0,[z0,z1,z2,z3,z924,z6]),(0,[z0,z1,z2,z324,z4,z416]),(0,[z135,z0,z158,z164,z4,z6])],[],[(0,[z0,z1,z2,z925,z4,z6]),(0,[z0,z2,z3,z926,z4,z6]),(0,[z0,z1,z600,z3,z74,z6])],[(0,[z58,z1,z2,z837,z4,z6]),(0,[z1,z2,z3,z837,z4,z6]),(0,[z0,z1,z2,z927,z4,z6]),(0,[z200,z80,z0,z3,z4,z6])],[(0,[z0,z1,z928,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z929]),(0,[z0,z1,z2,z3,z930,z6]),(0,[z0,z1,z2,z3,z931,z6]),(0,[z932,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z933,z6])],[(0,[z0,z1,z2,z24,z4,z130])]],
   [[(0,[z245,z7,z2,z3,z4,z6]),(0,[z0,z2,z205,z783,z4,z6])],[(0,[z0,z1,z2,z3,z934,z6]),(0,[z935,z1,z2,z3,z4,z6]),(0,[z936,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z937,z6]),(0,[z446,z0,z1,z3,z4,z23]),(0,[z0,z1,z2,z30,z3,z738])],[(0,[z0,z938,z1,z3,z4,z6]),(0,[z0,z1,z3,z939,z4,z6]),(0,[z550,z1,z2,z101,z4,z6]),(0,[z0,z1,z77,z3,z39,z6]),(0,[z0,z1,z2,z940,z4,z6]),(0,[z0,z1,z2,z3,z4,z941])],[(0,[z0,z261,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z151,z6]),(0,[z0,z1,z942,z3,z4,z6]),(0,[z0,z1,z2,z349,z3,z6])],[(0,[z0,z1,z2,z3,z943,z4]),(0,[z0,z1,z2,z3,z944,z6]),(0,[z0,z1,z663,z3,z4,z50]),(0,[z28,z0,z1,z2,z124,z6])],[(0,[z45,z389,z2,z3,z4,z6]),(0,[z0,z1,z2,z497,z3,z86]),(0,[z0,z158,z1,z349,z3,z6])],[],[(0,[z0,z193,z2,z3,z4,z197]),(0,[z0,z945,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z946,z4,z6]),(0,[z0,z261,z227,z3,z4,z6])],[(0,[z20,z852,z2,z3,z4,z6]),(0,[z0,z261,z231,z3,z4,z6]),(0,[z0,z1,z2,z947,z3,z4]),(0,[z948,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z949,z3,z4]),(0,[z58,z1,z2,z286,z101,z6]),(0,[z64,z0,z801,z3,z4,z6]),(0,[z0,z1,z950,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z951]),(0,[z0,z700,z2,z3,z4,z29])],[(0,[z0,z1,z2,z952,z4,z6]),(0,[z484,z38,z0,z1,z2,z6]),(0,[z0,z1,z231,z3,z4,z23]),(0,[z0,z1,z2,z324,z4,z6])],[(0,[z0,z1,z2,z953,z4,z6]),(0,[z0,z1,z2,z3,z954,z6]),(0,[z0,z1,z2,z153,z286,z3]),(0,[z0,z1,z2,z94,z4,z34]),(0,[z0,z1,z2,z3,z955,z4])],[(0,[z0,z1,z2,z3,z4,z777]),(0,[z0,z158,z1,z324,z4,z6]),(0,[z18,z0,z2,z3,z19,z6]),(0,[z0,z224,z1,z3,z4,z23])],[(0,[z0,z1,z2,z3,z4,z197])]],
   [[(0,[z0,z193,z2,z3,z86,z6]),(0,[z64,z0,z241,z72,z4,z6]),(0,[z0,z1,z956,z3,z4,z6]),(0,[z0,z2,z3,z750,z4,z6]),(0,[z0,z1,z2,z84,z206,z6]),(0,[z957,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z24,z75,z34])],[(0,[z1,z852,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z958])],[(0,[z0,z1,z2,z3,z4,z959]),(0,[z0,z1,z2,z3,z139,z4]),(0,[z0,z1,z2,z72,z4,z416])],[(0,[z0,z1,z2,z3,z960,z6]),(0,[z0,z1,z2,z961,z4,z6]),(0,[z0,z1,z411,z107,z4,z6]),(0,[z0,z1,z554,z3,z74,z6])],[],[(0,[z0,z1,z2,z3,z962,z6]),(0,[z1,z126,z766,z3,z4,z6]),(0,[z38,z1,z105,z3,z39,z6]),(0,[z1,z2,z3,z4,z129,z777]),(0,[z963,z1,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z303,z69]),(0,[z0,z964,z1,z2,z3,z4])],[(0,[z0,z1,z2,z965,z3,z6])],[(0,[z64,z0,z241,z3,z4,z416]),(0,[z0,z966,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z967]),(0,[z0,z1,z2,z4,z341,z69]),(0,[z0,z1,z2,z30,z3,z15])]],
   [[(0,[z0,z1,z2,z968,z4,z6]),(0,[z0,z1,z2,z3,z86,z6]),(0,[z0,z1,z385,z3,z74,z6]),(0,[z134,z0,z3,z4,z26,z300])],[(0,[z0,z1,z2,z3,z4,z969]),(0,[z263,z1,z3,z4,z6,z50]),(0,[z0,z1,z2,z3,z970,z6]),(0,[z0,z195,z1,z108,z4,z6])],[(0,[z64,z0,z677,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z971])],[(0,[z0,z1,z2,z3,z4,z972]),(0,[z21,z0,z2,z3,z4,z303]),(0,[z0,z2,z3,z783,z4,z6]),(0,[z134,z0,z2,z3,z4,z26]),(0,[z0,z1,z2,z4,z29,z271])],[(0,[z28,z0,z1,z77,z3,z6]),(0,[z0,z1,z2,z3,z4,z973]),(0,[z1,z2,z3,z4,z777,z22]),(0,[z974,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z975])],[(0,[z0,z1,z227,z3,z86,z6]),(0,[z0,z2,z3,z4,z26,z723])],[(0,[z0,z1,z2,z3,z4,z976]),(0,[z0,z1,z231,z3,z86,z6]),(0,[z0,z1,z2,z3,z750,z6]),(0,[z0,z1,z2,z3,z4,z431])],[(0,[z0,z1,z2,z3,z977,z6]),(0,[z795,z0,z1,z3,z4,z6]),(0,[z0,z1,z978,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z979,z4,z6]),(0,[z0,z1,z2,z206,z361,z6]),(0,[z135,z0,z165,z164,z4,z6]),(0,[z980,z1,z2,z3,z4,z6])],[(0,[z0,z981,z2,z3,z4,z6]),(0,[z0,z1,z2,z24,z181,z4])],[(0,[z0,z982,z2,z3,z4,z6]),(0,[z0,z1,z77,z3,z46,z6])],[(0,[z0,z1,z2,z55,z204,z6]),(0,[z200,z0,z3,z4,z6,z50]),(0,[z0,z1,z3,z983,z4,z6])],[(0,[z0,z314,z1,z2,z24,z4]),(0,[z0,z1,z984,z3,z4,z6]),(0,[z0,z1,z2,z72,z461,z6]),(0,[z985,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z986]),(0,[z80,z0,z1,z3,z4,z23])],[(0,[z0,z1,z2,z3,z987,z6]),(0,[z88,z1,z2,z3,z461,z6]),(0,[z0,z1,z2,z3,z4,z988]),(0,[z0,z1,z3,z4,z300,z6]),(0,[z0,z989,z2,z3,z4,z6])],[(0,[z0,z1,z2,z274,z4,z6]),(0,[z0,z1,z990,z3,z4,z6]),(0,[z0,z1,z2,z3,z86,z26]),(0,[z446,z0,z1,z3,z4,z416])],[(0,[z453,z1,z2,z3,z39,z6]),(0,[z0,z991,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z992])]],
   [[(0,[z0,z1,z2,z3,z993,z6]),(0,[z0,z1,z2,z3,z86,z29])],[(0,[z263,z1,z2,z324,z4,z6]),(0,[z64,z0,z241,z3,z461,z6]),(0,[z0,z994,z2,z3,z4,z6])],[(0,[z9,z1,z81,z3,z10,z6]),(0,[z0,z371,z2,z3,z4,z29]),(0,[z0,z1,z2,z3,z4,z995])],[(0,[z0,z1,z2,z3,z4,z996]),(0,[z0,z1,z2,z997,z4,z6]),(0,[z96,z1,z2,z3,z4,z284]),(0,[z0,z1,z2,z3,z461,z416]),(0,[z0,z1,z159,z107,z4,z6])],[(0,[z0,z1,z2,z3,z4,z998]),(0,[z0,z1,z999,z3,z4,z6]),(0,[z0,z1,z2,z24,z34,z358])],[(0,[z0,z1,z2,z3,z4,z230]),(0,[z0,z244,z1,z3,z217,z6]),(0,[z0,z1,z2,z1000,z3,z6]),(0,[z0,z1,z2,z3,z52,z6]),(0,[z0,z1,z2,z1001,z3,z4])],[(0,[z0,z1,z2,z1002,z4,z6]),(0,[z0,z1,z1003,z3,z4,z6]),(1,[z1,z2,z3,z4,z777]),(0,[z0,z158,z1,z107,z4,z6]),(0,[z0,z1,z1004,z3,z4,z6]),(0,[z0,z1,z2,z717,z4,z6])],[(0,[z0,z1,z2,z3,z1005,z6]),(0,[z0,z79,z2,z3,z67,z6])]],
   [[(0,[z0,z1006,z2,z3,z4,z6]),(0,[z0,z100,z1,z2,z24,z6]),(0,[z559,z1,z2,z3,z46,z6]),(0,[z0,z1,z1007,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1008]),(1,[z0,z1,z2,z4,z784])],[(0,[z446,z0,z3,z4,z6,z29]),(0,[z0,z1,z107,z717,z4,z6])],[(0,[z0,z1009,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z1010]),(0,[z0,z705,z1,z2,z4,z69])],[(0,[z20,z8,z2,z3,z4,z6]),(0,[z135,z0,z2,z349,z164,z6]),(0,[z0,z273,z1,z3,z720,z6])],[(0,[z202,z8,z2,z3,z4,z6])],[(0,[z0,z1,z2,z1011,z4,z6]),(0,[z0,z1,z3,z4,z291,z50]),(0,[z0,z1,z2,z30,z3,z86]),(0,[z0,z1,z2,z3,z4,z1012])],[(0,[z0,z1,z2,z3,z4,z1013]),(0,[z0,z1,z2,z497,z274,z4])]],
   [[(0,[z9,z1,z81,z3,z4,z6]),(0,[z0,z1,z2,z3,z1014,z6]),(0,[z0,z1,z2,z24,z4,z342]),(0,[z446,z0,z1,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z1015]),(0,[z1016,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z1017,z6]),(0,[z0,z1,z2,z1018,z3,z6]),(0,[z0,z193,z227,z3,z4,z6]),(0,[z0,z1,z1019,z3,z4,z6])],[(0,[z0,z193,z231,z3,z4,z6]),(0,[z1020,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z24,z4,z34])],[(0,[z0,z1,z2,z3,z4,z1021]),(0,[z0,z801,z241,z3,z4,z6]),(0,[z28,z0,z1,z2,z483,z6])],[(0,[z0,z1,z2,z3,z1022,z6]),(0,[z0,z1,z231,z3,z4,z291]),(0,[z58,z0,z100,z1,z2,z6]),(0,[z0,z1,z2,z3,z461,z6]),(0,[z0,z2,z3,z4,z376,z29]),(0,[z0,z1,z2,z3,z4,z1023]),(0,[z0,z1,z2,z3,z1024,z4]),(0,[z0,z1,z2,z3,z1025,z6])],[(0,[z0,z1,z2,z324,z4,z114]),(0,[z0,z68,z1,z2,z4,z69])],[(0,[z1,z2,z3,z760,z39,z6]),(0,[z0,z158,z1,z3,z4,z1023]),(0,[z0,z1026,z2,z3,z4,z6])]],
   [[(0,[z96,z1,z2,z3,z4,z777]),(0,[z0,z1,z2,z3,z216,z6])],[(0,[z0,z1,z2,z3,z1027,z6]),(0,[z0,z1,z2,z1028,z3,z4]),(0,[z0,z1,z1029,z3,z4,z6]),(0,[z0,z1,z2,z206,z6,z280])],[(0,[z21,z1,z2,z55,z4,z22]),(0,[z0,z1,z1030,z3,z4,z6]),(0,[z0,z1,z2,z522,z4,z34])],[(0,[z0,z1,z231,z3,z4,z6]),(0,[z0,z1,z2,z3,z14,z128]),(0,[z0,z1,z3,z4,z118,z50])],[(0,[z453,z1,z81,z3,z4,z6]),(0,[z0,z1,z3,z4,z1031,z6])],[(0,[z0,z1,z2,z837,z4,z6]),(0,[z0,z193,z2,z3,z4,z29]),(0,[z0,z1,z231,z181,z4,z6]),(0,[z64,z0,z1,z3,z4,z35])],[(0,[z0,z100,z1,z2,z6,z69]),(0,[z0,z1,z2,z1032,z4,z6]),(0,[z0,z1,z2,z24,z75,z6])],[(0,[z1033,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z23,z724])]],
   [[(0,[z0,z1,z3,z1034,z4,z6]),(0,[z0,z1,z1035,z3,z4,z6]),(0,[z0,z261,z2,z181,z4,z6]),(0,[z0,z163,z2,z783,z4,z6]),(0,[z1036,z0,z2,z3,z4,z6])],[(0,[z80,z0,z1,z3,z4,z416])],[(0,[z0,z1,z2,z3,z1037,z6])],[(0,[z0,z1,z2,z3,z1038,z6]),(0,[z484,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z181,z4,z23]),(0,[z1039,z1,z2,z3,z4,z6]),(1,[z0,z2,z3,z750,z6]),(0,[z18,z0,z2,z3,z565,z6]),(0,[z0,z1,z2,z1040,z4,z6]),(0,[z0,z68,z1,z2,z4,z784])],[(0,[z28,z0,z1,z2,z425,z6]),(0,[z0,z79,z2,z3,z67,z266]),(0,[z0,z657,z2,z3,z67,z6])],[(0,[z0,z1,z2,z3,z4,z1041]),(0,[z0,z1,z3,z4,z300,z69])],[(0,[z0,z1,z2,z1042,z4,z6]),(0,[z0,z1,z2,z1043,z3,z6])],[(0,[z0,z1,z2,z3,z1044,z6]),(0,[z88,z1,z2,z72,z4,z6]),(0,[z0,z1045,z2,z3,z4,z6]),(0,[z0,z1,z2,z4,z6,z784])]],
   [[(0,[z0,z100,z1,z2,z153,z3]),(0,[z38,z1,z2,z274,z39,z6]),(0,[z0,z1,z2,z1046,z4,z6]),(0,[z0,z261,z2,z3,z204,z6]),(0,[z0,z1,z2,z4,z26,z271]),(0,[z0,z1,z575,z3,z4,z50])],[(0,[z337,z8,z2,z3,z4,z6])],[(0,[z0,z1,z227,z3,z4,z29]),(0,[z0,z1,z107,z324,z4,z6]),(0,[z64,z155,z0,z3,z4,z6]),(0,[z0,z1,z3,z217,z720,z6]),(0,[z0,z1,z2,z3,z4,z738])],[(0,[z0,z1047,z2,z3,z4,z6]),(1,[z0,z1,z717,z4,z6])],[(0,[z0,z314,z1,z2,z286,z3]),(0,[z21,z1,z2,z404,z3,z4]),(0,[z0,z1,z2,z3,z1048,z6]),(0,[z0,z1,z2,z324,z194,z6]),(0,[z0,z1,z2,z84,z3,z143])],[(0,[z184,z1,z81,z3,z4,z6]),(0,[z80,z0,z1,z3,z4,z291]),(0,[z0,z1,z2,z3,z29,z358]),(0,[z0,z1,z2,z3,z75,z6])],[(0,[z0,z1,z2,z1049,z4,z6]),(0,[z88,z1,z2,z3,z4,z416]),(0,[z0,z1,z2,z72,z4,z114]),(0,[z0,z1,z2,z1050,z4,z6])],[(0,[z1051,z0,z1,z2,z4,z6]),(0,[z0,z1052,z2,z3,z4,z6]),(0,[z484,z38,z1,z2,z39,z6]),(0,[z0,z1,z2,z497,z3,z14]),(0,[z0,z1,z2,z24,z515,z4]),(0,[z64,z88,z241,z3,z4,z6]),(0,[z0,z1,z2,z4,z835,z6])]],
   [[(0,[z0,z1,z2,z1053,z3,z4]),(0,[z0,z2,z3,z4,z197,z29])],[(0,[z132,z1,z597,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1054]),(0,[z0,z1,z1055,z3,z4,z6]),(0,[z0,z2,z3,z4,z1056,z6])],[(0,[z0,z1,z1057,z3,z4,z6]),(0,[z263,z1,z2,z3,z461,z6]),(0,[z0,z1,z2,z3,z4,z1058]),(0,[z0,z1,z492,z3,z74,z6])],[(0,[z1059,z0,z2,z3,z4,z6]),(0,[z64,z0,z241,z3,z4,z114]),(0,[z0,z1,z2,z3,z4,z723])],[(0,[z1060,z0,z2,z3,z4,z6]),(0,[z0,z158,z1,z3,z4,z1058]),(0,[z0,z1,z2,z3,z6,z1061])],[(0,[z0,z1,z1062,z3,z4,z6]),(0,[z0,z1,z1063,z3,z4,z6]),(0,[z0,z1,z2,z181,z86,z6]),(0,[z0,z1064,z1,z3,z4,z6]),(0,[z1065,z0,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z1066,z6]),(0,[z0,z1,z1067,z3,z4,z6]),(0,[z0,z1,z2,z84,z835,z6])],[(0,[z1,z2,z3,z46,z760,z6])]],
   [[(0,[z28,z0,z1,z2,z3,z143]),(0,[z0,z1,z3,z4,z724,z6])],[(0,[z0,z149,z1,z2,z4,z69])],[(0,[z0,z1,z2,z1068,z4,z6]),(0,[z226,z1,z2,z837,z4,z6]),(0,[z484,z0,z1,z2,z74,z6]),(0,[z0,z1,z3,z165,z4,z6])],[],[(0,[z188,z1,z2,z3,z447,z6]),(0,[z0,z1,z1069,z2,z3,z4])],[(1,[z1,z2,z837,z4,z6]),(0,[z0,z1,z2,z3,z4,z1070])],[(0,[z0,z1,z2,z1071,z4,z6]),(0,[z556,z1,z2,z32,z4,z6]),(0,[z38,z1,z2,z3,z760,z6])],[(0,[z1,z766,z81,z3,z4,z6]),(0,[z484,z0,z1,z2,z6,z15]),(0,[z96,z1,z2,z3,z4,z258]),(0,[z0,z1,z2,z72,z4,z6])]],
   [[(0,[z88,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1072,z6]),(0,[z134,z263,z2,z3,z4,z6]),(0,[z135,z0,z2,z783,z4,z6])],[(0,[z0,z1,z2,z1073,z4,z6]),(0,[z0,z1074,z2,z3,z4,z6])],[(0,[z45,z852,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1075,z6]),(0,[z484,z0,z1,z2,z14,z6]),(0,[z0,z1,z2,z571,z4,z6]),(0,[z28,z0,z1,z2,z835,z6])],[(0,[z0,z1,z49,z3,z4,z724])],[(0,[z0,z2,z3,z4,z291,z747]),(0,[z64,z0,z241,z3,z4,z6]),(0,[z0,z1,z2,z72,z194,z6]),(0,[z0,z1,z2,z630,z3,z15]),(1,[z0,z1,z2,z835,z6])],[(0,[z0,z1,z1076,z3,z4,z6]),(0,[z38,z1,z2,z3,z139,z39]),(0,[z0,z1,z2,z497,z3,z4])],[(0,[z0,z1,z2,z3,z1077,z6]),(0,[z0,z1,z2,z3,z1078,z6]),(0,[z0,z1,z2,z3,z1079,z4]),(0,[z0,z1,z2,z3,z4,z416])],[(0,[z0,z1,z2,z3,z1080,z6]),(0,[z21,z261,z2,z3,z4,z22]),(0,[z0,z1,z2,z3,z461,z114]),(0,[z0,z1,z2,z3,z4,z1081])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 553) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 553).take 511) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1064)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [553, 511] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_nil pbend))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 169).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 169).take 87).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [169, 87] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_nil pcend))

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

end PEqualNP.Outside.L_meta_46062

theorem PEqualNP.Outside.L_meta_46062 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074602 * 2 ^ 32 + 4243126400) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074602 * 2 ^ 32 + 4243126400) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_46062.solve