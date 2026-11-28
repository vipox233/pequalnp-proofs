import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_43156

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
  Nat.testBit (4276808362 * 2 ^ 32 + 3941132800) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x800004055061b856#64 ++ 0xa000010154186e15#64 ++ 0x60023c7ff3e3f8ff#64 ++ 0xd8008f1ffcf8fe3f#64 : BitVec 256),
   (0x041cd1acc52c5b30#64 ++ 0xc107346b314b16cc#64 ++ 0xfc3dd3accd3c7f33#64 ++ 0xbf0f74eb334f1fcc#64 : BitVec 256),
   (0x09c162cf0a368dc3#64 ++ 0x027058b3c28da370#64 ++ 0xefc1e3cf0e3f8fc3#64 ++ 0x7bf078f3c38fe3f0#64 : BitVec 256),
   (0x02ee03700f8006a8#64 ++ 0x00bb80dc03e001aa#64 ++ 0xfffe03f00fc00ffe#64 ++ 0xffff80fc03f003ff#64 : BitVec 256),
   (0x1377bc000fdb6000#64 ++ 0x04ddef0003f6d800#64 ++ 0xf7fffc000ffff001#64 ++ 0xfdffff0003fffc00#64 : BitVec 256),
   (0x03bbfbfaa0000000#64 ++ 0x00eefefea8000000#64 ++ 0xdbfffffff0000003#64 ++ 0xf6fffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [1, 2]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [8, 4]⟩, ⟨.and, [9, 3]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [9, 3]⟩, ⟨.and, [7, 12]⟩, ⟨.and, [11, 5]⟩, ⟨.or, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0014900005084000 0x0005240001421000 0xf43dd0000d3c7001 0xbd0f7400034f1c00

def z1 : W := mkw 0x02e202500a800488 0x00b8809402a00122 0x03c2005002c000cc 0x40f0801400b00033

def z2 : W := mkw 0x02ee03700f8006a8 0x00bb80dc03e001aa 0xfffe03f00fc00ffe 0xffff80fc03f003ff

def z3 : W := mkw 0x03bbfbfaa0000000 0x00eefefea8000000 0xdbfffffff0000003 0xf6fffffffc000000

def z4 : W := mkw 0x09c162cf0a368dc3 0x027058b3c28da370 0xefc1e3cf0e3f8fc3 0x7bf078f3c38fe3f0

def z5 : W := mkw 0x1377bc000fdb6000 0x04ddef0003f6d800 0xf7fffc000ffff001 0xfdffff0003fffc00

def z6 : W := mkw 0x800004055061b856 0xa000010154186e15 0x60023c7ff3e3f8ff 0xd8008f1ffcf8fe3f

def z7 : W := mkw 0x00880370000006a8 0x002200dc000001aa 0x080003f000000ffe 0x020000fc000003ff

def z8 : W := mkw 0x041cd1acc52c5b30 0xc107346b314b16cc 0xfc3dd3accd3c7f33 0xbf0f74eb334f1fcc

def z9 : W := mkw 0x0018912080000000 0x0006244820000000 0x103c1020c0000000 0x840f040830000000

def z10 : W := mkw 0x0323280000000000 0x00c8ca0000000000 0x03c22c0000000000 0x40f08b0000000000

def z11 : W := mkw 0x022e013005800228 0x008b804c0160008a 0x103e003001c0003c 0x840f800c0070000f

def z12 : W := mkw 0x0901608f00368943 0x02405823c00da250 0x0001e00f003f8001 0x00007803c00fe000

def z13 : W := mkw 0x0000000000000000 0x0000000000000000 0x6002007003c008fe 0xd800801c00f0023f

def z14 : W := mkw 0x03bbfbfaa0000000 0x00eefefea8000000 0x9bfdff8ff0000001 0x26ff7fe3fc000000

def z15 : W := mkw 0x041cd1acc52c5b30 0xc107346b314b16cc 0x9c3dd38ccc3c7701 0x270f74e3330f1dc0

def z16 : W := mkw 0x0be32a532a1284c3 0x02f8ca94ca84a130 0x03c22c53320380c0 0x40f08b14cc80e030

def z17 : W := mkw 0x800004055061b856 0xa000010154186e15 0x2000007ff3e3f8fe 0x0800001ffcf8fe3f

def z18 : W := mkw 0x008843faa0000000 0x002210fea8000000 0x080003fff0000002 0x020000fffc000000

def z19 : W := mkw 0x104404000fdb6000 0x0411010003f6d800 0x240000000ffff000 0x0900000003fffc00

def z20 : W := mkw 0x041cd1a8850c4320 0x4107346a214310c8 0x9c3dc3800c1c0700 0x270f70e0030701c0

def z21 : W := mkw 0x13632c000ad32000 0x04d8cb0002b4c800 0x03c22c0002c38000 0x40f08b0000b0e000

def z22 : W := mkw 0x023a9930a0000000 0x008ea64c28000000 0x503e3c7ff0000003 0xd40f8f1ffc000000

def z23 : W := mkw 0x004400000f8006a8 0x0011000003e001aa 0x240000000fc00ffc 0x0900000003f003ff

def z24 : W := mkw 0x1333bc00005b6000 0x04ccef000016d800 0xd3fffc00003ff001 0xf4ffff00000ffc00

def z25 : W := mkw 0x00c402400f8006a8 0x0031009003e001aa 0xefc003c00fc00ffe 0x7bf000f003f003ff

def z26 : W := mkw 0x07bffbfee52c5b30 0xc1effeffb94b16cc 0xfffffffffd3c7f33 0xffffffffff4f1fcc

def z27 : W := mkw 0x03fffbfaaf8006a8 0x00fffefeabe001aa 0xffffffffffc00fff 0xfffffffffff003ff

def z28 : W := mkw 0x13672c000fd32000 0x04d9cb0003f4c800 0xf7fe2c000fc38000 0xfdff8b0003f0e000

def z29 : W := mkw 0x03bbfbfaa0000000 0x00eefefea8000000 0xfbfffffff3c008ff 0xfefffffffcf0023f

def z30 : W := mkw 0x000841a880000000 0x0002106a20000000 0x080003acc0000002 0x020000eb30000000

def z31 : W := mkw 0x0c4400054f3edff3 0xc311000153cfb7fc 0x240000000f3ffff0 0x0900000003cffffc

def z32 : W := mkw 0x02e202500a800488 0x00b8809402a00122 0x63c2007003c008fe 0xd8f0801c00f0023f

def z33 : W := mkw 0x026604000fc12000 0x0099810003f04800 0xf7fe3c000fe3f001 0xfdff8f0003f8fc00

def z34 : W := mkw 0x063e9930e5085230 0xc18fa64c3942148c 0x103e1c30f1007030 0x840f870c3c401c0c

def z35 : W := mkw 0x114524000fdb6000 0x0451490003f6d800 0xe7c1e0000ffff001 0x79f0780003fffc00

def z36 : W := mkw 0x0000408c00240900 0x0000102300090240 0x0800038c00000f02 0x020000e3000003c0

def z37 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000102cc0000003 0x9000040b30000000

def z38 : W := mkw 0x13fffbfaaf9a4000 0x04fffefeabe69000 0x9ffdc3800c1c0000 0x27ff70e003070000

def z39 : W := mkw 0x83a32e533041a046 0x20e8cb94cc106811 0x03c22c5332c380cc 0x40f08b14ccb0e033

def z40 : W := mkw 0x008c0370050006a8 0x002300dc014001aa 0xfc3c03f00d000ffe 0xbf0f00fc034003ff

def z41 : W := mkw 0x000c41ac05240b20 0x0003106b014902c8 0xfc3dc3ac0d3c0f33 0xbf0f70eb034f03cc

def z42 : W := mkw 0x800004011041a046 0x2000010044106811 0x00022c5332c380cc 0x40008b14ccb0e033

def z43 : W := mkw 0x841cd5add56dfb76 0xe107356b755b7edd 0xfc3fffffffffffff 0xff0fffffffffffff

def z44 : W := mkw 0x04000004402c5910 0xc1000001100b1644 0x00000000003c7000 0x00000000000f1c00

def z45 : W := mkw 0x0111f88aa0000000 0x00447e22a8000000 0x0001c00000000000 0x0000700000000000

def z46 : W := mkw 0x02ea03700a800488 0x00ba80dc02a00122 0xdbfe03f002c000ce 0xf6ff80fc00b00033

def z47 : W := mkw 0x03ffbb700f8006a8 0x00ffeedc03e001aa 0xfffffff00fc00fff 0xfffffffc03f003ff

def z48 : W := mkw 0x8333bc055061b856 0xa0ccef0154186e15 0xf3fffc7ff3e3f8ff 0xfcffff1ffcf8fe3f

def z49 : W := mkw 0x098162cf00248dc3 0x026058b3c0092370 0xcbc1e3cf00000fc3 0x72f078f3c00003f0

def z50 : W := mkw 0x0088037000000000 0x002200dc00000000 0x080003f000000002 0x020000fc00000000

def z51 : W := mkw 0x00c002400a000480 0x0030009002800120 0x8fc003800c000700 0x23f000e0030001c0

def z52 : W := mkw 0x17fffffeefff7b30 0xc5ffffffbbffdecc 0xffffffffffffff33 0xffffffffffffffcc

def z53 : W := mkw 0x84040405556dfb76 0xe1010101555b7edd 0x64023c7fffffffff 0xd9008f1fffffffff

def z54 : W := mkw 0x8000040050413014 0xa000010014104c05 0x00021c30f1c0703c 0x8000870c3c701c0f

def z55 : W := mkw 0x89c166cf5a77bdd7 0xa27059b3d69def75 0xefc3ffffffffffff 0xfbf0ffffffffffff

def z56 : W := mkw 0x0000040000412000 0x0000010000104800 0x60023c0003e3f001 0xd8008f0000f8fc00

def z57 : W := mkw 0x0111f88aa0000000 0x00447e22a8000000 0x0001fc0ff0000001 0x00007f03fc000000

def z58 : W := mkw 0x83bbfffff061b856 0xa0eefffffc186e15 0xfbfffffff3e3f8ff 0xfefffffffcf8fe3f

def z59 : W := mkw 0x82ee07755fe1befe 0xa0bb81dd57f86fbf 0xfffe3fffffe3ffff 0xffff8ffffff8ffff

def z60 : W := mkw 0x041c9120c5085230 0xc10724483142148c 0x103c1020c1007030 0x840f040830401c0c

def z61 : W := mkw 0x177ffdaccfff7b30 0xc5dfff6b33ffdecc 0xffffffaccfffff33 0xffffffeb33ffffcc

def z62 : W := mkw 0x004000000a800488 0x0010000002a00122 0x0000000002c000cc 0x0000000000b00033

def z63 : W := mkw 0x13e32e500ad32488 0x04f8cb9402b4c922 0x03c22c5002c380cc 0x40f08b1400b0e033

def z64 : W := mkw 0x02aa0370000006a8 0x00aa80dc000001aa 0xdbfe03f000000ffe 0xf6ff80fc000003ff

def z65 : W := mkw 0x026600000f800000 0x0099800003e00000 0xf7fe00000fc00000 0xfdff800003f00000

def z66 : W := mkw 0x1111bc00005b6000 0x04446f000016d800 0x0001fc00003ff001 0x00007f00000ffc00

def z67 : W := mkw 0x804404055fe1befe 0xa011010157f86fbf 0x240000000fe3fffc 0x0900000003f8ffff

def z68 : W := mkw 0x9377bc055ffbf856 0xa4ddef0157fefe15 0xf7fffc0ffffff001 0xfdffff03fffffc00

def z69 : W := mkw 0x0000000000000000 0x0000000000000000 0x00021c30f0000000 0x8000870c3c000000

def z70 : W := mkw 0x02e602500f800488 0x00b9809403e00122 0xf7fe00500fc000cc 0xfdff801403f00033

def z71 : W := mkw 0x93632c055af3b856 0xa4d8cb0156bcee15 0x63c23c7ff3e3f8ff 0xd8f08f1ffcf8fe3f

def z72 : W := mkw 0x06fed3fccfac5fb8 0xc1bfb4ff33eb17ee 0xffffd3fccffc7fff 0xfffff4ff33ff1fff

def z73 : W := mkw 0x0901608f00368943 0x02405823c00da250 0x6001e04f023f88c3 0x58007813c08fe230

def z74 : W := mkw 0x07bffbfee52c5b30 0xc1effeffb94b16cc 0xfffdd3accd3c7f33 0xbfff74eb334f1fcc

def z75 : W := mkw 0x09c162ca0a160581 0x027058b282858160 0x8fc1c3800c1c0700 0x23f070e0030701c0

def z76 : W := mkw 0x0dddf3efcf3edff3 0xc3777cfbf3cfb7fc 0xfffdf3efcf3ffff3 0xffff7cfbf3cffffc

def z77 : W := mkw 0x0000000500208842 0x0000000140082210 0x6000204f022388c3 0x58000813c088e230

def z78 : W := mkw 0x041cd1adc52cdb72 0xc107346b714b36dc 0xfc3df3efcf3ffff3 0xff0f7cfbf3cffffc

def z79 : W := mkw 0x03bbfbfaa0000000 0x00eefefea8000000 0xdbffff8000000001 0xf6ffffe000000000

def z80 : W := mkw 0x13ffbf700fdb66a8 0x04ffefdc03f6d9aa 0xfffffff00fffffff 0xfffffffc03ffffff

def z81 : W := mkw 0x841cd5acd56d7b34 0xe107356b355b5ecd 0xfc3fdfbcfdfc7f3f 0xbf0ff7ef3f7f1fcf

def z82 : W := mkw 0x00000000000006a8 0x00000000000001aa 0x0000000000000ffc 0x00000000000003ff

def z83 : W := mkw 0x1337bc0005db6000 0x04cdef000176d800 0x103ffc0001fff001 0x840fff00007ffc00

def z84 : W := mkw 0x0199fbfaa0000000 0x00667efea8000000 0x0801fffff0000003 0x02007ffffc000000

def z85 : W := mkw 0x033bf9a880000000 0x00cefe6a20000000 0xdbffffacc0000003 0xf6ffffeb30000000

def z86 : W := mkw 0x800004011041a046 0x2000010044106811 0x60023c5333e3f0cd 0xd8008f14ccf8fc33

def z87 : W := mkw 0x014120000a120000 0x0050480002848000 0xe7c1e0000e3f8001 0x79f07800038fe000

def z88 : W := mkw 0x1bf7fecf0fffedc3 0x06fdffb3c3fffb70 0xffffffcf0fffffc3 0xfffffff3c3fffff0

def z89 : W := mkw 0x13ffbb700f9a46a8 0x04ffeedc03e691aa 0xffffc3f00fdc0ffe 0xfffff0fc03f703ff

def z90 : W := mkw 0x026e01300f800228 0x009b804c03e0008a 0xf7fe00300fc0003c 0xfdff800c03f0000f

def z91 : W := mkw 0x0333f88aa0000000 0x00ccfe22a8000000 0xd3fffc0ff0000001 0xf4ffff03fc000000

def z92 : W := mkw 0x03ef63fa0f8006a8 0x00fbd8fe83e001aa 0xffffe3ff0fc00fff 0xfffff8ffc3f003ff

def z93 : W := mkw 0x041c9120c5085230 0xc10724483142148c 0xfc3c13a0cd007f32 0xbf0f04e833401fcc

def z94 : W := mkw 0x13ffbb700f9a46a8 0x04ffeedc03e691aa 0x9ffdc3800c1c0700 0x27ff70e0030701c0

def z95 : W := mkw 0x89c166cf1a77adc7 0x227059b3c69deb71 0xefc3efdf3eff8fcf 0x7bf0fbf7cfbfe3f3

def z96 : W := mkw 0x088042cf00248dc3 0x022010b3c0092370 0x080003cf00000fc2 0x020000f3c00003f0

def z97 : W := mkw 0x1bf7feca0fdf6581 0x06fdffb283f7d960 0xffffff800ffff701 0xffffffe003fffdc0

def z98 : W := mkw 0x8901648f5077b957 0xa2405923d41dee55 0x6003fc7ff3fff8ff 0xd800ff1ffcfffe3f

def z99 : W := mkw 0x0840408d0a368dc3 0x02101023428da370 0xec01c38c0e3f8fc3 0x3b0070e3038fe3f0

def z100 : W := mkw 0x004400000f8006a8 0x0011000003e001aa 0x640200700fc00ffe 0xd900801c03f003ff

def z101 : W := mkw 0x8000000550209856 0xa000000154082615 0x6000107ff12078ff 0x9800041ffc481e3f

def z102 : W := mkw 0x02aa037000000000 0x00aa80dc00000000 0xdbfe03f000000002 0xf6ff80fc00000000

def z103 : W := mkw 0x8bef67ff5ff7bfff 0xa2fbd9ffd7fdefff 0xffffffffffffffff 0xffffffffffffffff

def z104 : W := mkw 0x041cd1acc52c5b30 0xc107346b314b16cc 0x9c3dc3accc1c0f32 0x270f70eb330703cc

def z105 : W := mkw 0x02a2025000000000 0x00a8809400000000 0x03c2005000000000 0x40f0801400000000

def z106 : W := mkw 0x000c012445201a30 0x800300491148068c 0xfc3c13accd207f33 0xbf0f04eb33481fcc

def z107 : W := mkw 0x001c912005084220 0x0007244801421088 0xfc3dd3a00d3c7f33 0xbf0f74e8034f1fcc

def z108 : W := mkw 0x1377bc000fdb6000 0x04ddef0003f6d800 0x97fdfc000c3ff001 0x25ff7f00030ffc00

def z109 : W := mkw 0x841cd5add56dfb76 0xe107356b755b7edd 0xfc3dffaffd3fff33 0xbf0f7febff4fffcc

def z110 : W := mkw 0x0404000045085230 0xc10100001142148c 0x0000000001007030 0x0000000000401c0c

def z111 : W := mkw 0x0bef63ff0fb68feb 0x02fbd8ffc3eda3fa 0xffffe3ff0fff8fff 0xfffff8ffc3ffe3ff

def z112 : W := mkw 0x0be762cf0fb68dc3 0x02f9d8b3c3eda370 0xffffe3cf0fff8fc3 0xfffff8f3c3ffe3f0

def z113 : W := mkw 0x067ed1accfac5b30 0xc19fb46b33eb16cc 0xffffd3accffc7f33 0xfffff4eb33ff1fcc

def z114 : W := mkw 0x018162ca00000000 0x006058b280000000 0xcbc1e3cf00000003 0x72f078f3c0000000

def z115 : W := mkw 0x084000050a368dc3 0x02100001428da370 0x240000000e3f8fc0 0x09000000038fe3f0

def z116 : W := mkw 0x104404000fdb6000 0x0411010003f6d800 0x64023c000ffff001 0xd9008f0003fffc00

def z117 : W := mkw 0x8000000550209856 0xa000000154082615 0x0000007ff00008fe 0x0000001ffc00023f

def z118 : W := mkw 0x9377bc055ffbf856 0xa4ddef0157fefe15 0xf7fffc7ffffff8ff 0xfdffff1ffffffe3f

def z119 : W := mkw 0x1bf7facf0fbecdc3 0x06fdfeb3c3efb370 0xfffde3cf0e3f8fc3 0x7fff78f3c38fe3f0

def z120 : W := mkw 0x01c122400a120480 0x0070489002848120 0xefc1e3c00e3f8fc3 0x7bf078f0038fe3f0

def z121 : W := mkw 0x084000010a1284c3 0x021000004284a130 0x00000000020380c0 0x000000000080e030

def z122 : W := mkw 0x1377bc000fdb6000 0x04ddef0003f6d800 0xf7fffc700ffff8ff 0xfdffff1c03fffe3f

def z123 : W := mkw 0x0018d1a880000000 0x0006346a20000000 0xd83dd3acc0000003 0xb60f74eb30000000

def z124 : W := mkw 0x1bf7be430fdbe4c3 0x06fdef90c3f6f930 0xf7fffc430ffff0c1 0xfdffff10c3fffc30

def z125 : W := mkw 0x03bbfbfaa0000000 0x00eefefea8000000 0x9bffefd330000000 0x66fffbf4cc000000

def z126 : W := mkw 0x87bffffff56dfb76 0xe1effffffd5b7edd 0xffffffffffffffff 0xffffffffffffffff

def z127 : W := mkw 0x09c162cf4a369dd3 0x827058b3d28da774 0xefc1f3efcf3ffff3 0xfbf07cfbf3cffffc

def z128 : W := mkw 0x040841acc0241b30 0xc102106b300906cc 0xec01c3accc3c0f33 0x3b0070eb330f03cc

def z129 : W := mkw 0x02aa037000000000 0x00aa80dc00000000 0xdbfe3ffff0000003 0xf6ff8ffffc000000

def z130 : W := mkw 0x02ea03700a000480 0x00ba80dc02800120 0xfffe03f00e000fc2 0xffff80fc038003f0

def z131 : W := mkw 0x045cd1accfac5fb8 0xc117346b33eb17ee 0xfc3dd3accffc7fff 0xbf0f74eb33ff1fff

def z132 : W := mkw 0x0bfbfbffaa368dc3 0x02fefeffea8da370 0xfffffffffe3f8fc3 0xffffffffff8fe3f0

def z133 : W := mkw 0x808847fff061b856 0xa02211fffc186e15 0x68023ffff3e3f8ff 0xda008ffffcf8fe3f

def z134 : W := mkw 0x09c162ca0a160581 0x027058b282858160 0xefc1e3800e3f8701 0x7bf078e0038fe1c0

def z135 : W := mkw 0x027690000f884000 0x009da40003e21000 0xf7ffd0000ffc7001 0xfdfff40003ff1c00

def z136 : W := mkw 0x03bbfbfaa00006a8 0x00eefefea80001aa 0xdbfffffff0000fff 0xf6fffffffc0003ff

def z137 : W := mkw 0x0dddf3ea8f1e47a1 0x43777cfaa3c791e8 0x9ffdc3800c1c0700 0x27ff70e0030701c0

def z138 : W := mkw 0x0000000440201810 0x8000000110080604 0x6000102cc1207833 0x9800040b30481e0c

def z139 : W := mkw 0x004000000a000480 0x0010000002800120 0x240000000e000fc0 0x09000000038003f0

def z140 : W := mkw 0x0410d08cc02c5910 0xc1043423300b1644 0x0001d00cc03c7001 0x00007403300f1c00

def z141 : W := mkw 0x1377b8000f9a4000 0x04ddee0003e69000 0x97fdc0000c1c0000 0x25ff700003070000

def z142 : W := mkw 0x03a32a5220000000 0x00e8ca9488000000 0x03c22c5330000000 0x40f08b14cc000000

def z143 : W := mkw 0x0be36adf2a368dc3 0x02f8dab7ca8da370 0xefc3efdf3e3f8fc3 0x7bf0fbf7cf8fe3f0

def z144 : W := mkw 0x07bffbfae5085230 0xc1effefeb942148c 0xdbfffffff1007033 0xf6fffffffc401c0c

def z145 : W := mkw 0x1be32e430ad3a4c3 0x06f8cb90c2b4e930 0x03c22c4302c380c0 0x40f08b10c0b0e030

def z146 : W := mkw 0x163eddacc5ed7b30 0xc58fb76b317b5ecc 0xfc3fdfaccdfc7f33 0xbf0ff7eb337f1fcc

def z147 : W := mkw 0x808807755061befe 0xa02201dd54186fbf 0x68023ffff3e3ffff 0xda008ffffcf8ffff

def z148 : W := mkw 0x09c162ca0a160581 0x027058b282858160 0xefc1c3c00e1c0fc2 0x7bf070f0038703f0

def z149 : W := mkw 0x1377bc000fdb6000 0x04ddef0003f6d800 0xf7fffc7ffffff003 0xfdffff1ffffffc00

def z150 : W := mkw 0x8000040450613814 0xa000010114184e05 0x60021c3cf1e0783f 0x9800870f3c781e0f

def z151 : W := mkw 0x12369c0005c96000 0x048da70001725800 0x103e1c0001c07000 0x840f870000701c00

def z152 : W := mkw 0x000004050061a842 0x0000010140186a10 0x60023c4f03e3f8c3 0xd8008f13c0f8fe30

def z153 : W := mkw 0x9377bc005fdb7014 0xa4ddef0017f6dc05 0xf7fffc30fffff03d 0xfdffff0c3ffffc0f

def z154 : W := mkw 0x0d1df1afc53edb73 0xc3477c6bf14fb6dc 0xfc3df3afcd3fff33 0xbf0f7cebf34fffcc

def z155 : W := mkw 0x049cd3fee52c5b30 0xc12734ffb94b16cc 0xfc3dd3fffd3c7f33 0xbf0f74ffff4f1fcc

def z156 : W := mkw 0x041cd1acc52c5b30 0xc107346b314b16cc 0xbc3dc3800d3c7f30 0x2f0f70e0034f1fcc

def z157 : W := mkw 0x02ee03750fa08eea 0x00bb80dd43e823ba 0xfffe23ff0fe38fff 0xffff88ffc3f8e3ff

def z158 : W := mkw 0x0333b80000000000 0x00ccee0000000000 0xd3fffc0000000001 0xf4ffff0000000000

def z159 : W := mkw 0x800004051061a846 0x2000010144186a11 0x60022c5f32e388cf 0x58008b17ccb8e233

def z160 : W := mkw 0x00c002400a000480 0x0030009002800120 0xefc003c00e000fc2 0x7bf000f0038003f0

def z161 : W := mkw 0x084000000a160581 0x0210000002858160 0x040000000c1c0700 0x01000000030701c0

def z162 : W := mkw 0x9377bc011fdbe046 0x24ddef0047f6f811 0xf7fffc533ffff0cd 0xfdffff14cffffc33

def z163 : W := mkw 0x1111fc8aa05b6000 0x04447f22a816d800 0x0001fc0ff03ff001 0x00007f03fc0ffc00

def z164 : W := mkw 0x1377bc044ffb7810 0x84ddef0113fede04 0xf7fffc2ccffff833 0xfdffff0b33fffe0c

def z165 : W := mkw 0x1377bc000fdb6000 0x04ddef0003f6d800 0x97ffec000edf8000 0x65fffb0003b7e000

def z166 : W := mkw 0x03fffbfaaf8006a8 0x00fffefeabe001aa 0x9ffdc3800c000700 0x27ff70e0030001c0

def z167 : W := mkw 0x0941608f0a368943 0x02505823c28da250 0xe7c1e00f0e3f8001 0x79f07803c38fe000

def z168 : W := mkw 0x0004000005084000 0x0001000001421000 0x240000000d3c7000 0x09000000034f1c00

def z169 : W := mkw 0x800004055061b856 0xa000010154186e15 0x00023c5ff2e3f0cd 0x40008f17fcb8fc33

def z170 : W := mkw 0x023e9930a5800228 0x008fa64c2960008a 0x103e1c30f1c0003c 0x840f870c3c70000f

def z171 : W := mkw 0x02ee43faaf8006a8 0x00bb90feabe001aa 0xfffe03ffffc00ffe 0xffff80fffff003ff

def z172 : W := mkw 0x09c162cf0a368dc3 0x027058b3c28da370 0xefc3fffffe3f8fc3 0xfbf0ffffff8fe3f0

def z173 : W := mkw 0x02badbfaa0000000 0x00aeb6fea8000000 0x183e1ffff0000002 0x860f87fffc000000

def z174 : W := mkw 0x904404055ffbf856 0xa411010157fefe15 0x240000000ffff8fc 0x0900000003fffe3f

def z175 : W := mkw 0x000c012005000220 0x0003004801400088 0xfc3c03a00d000f32 0xbf0f00e8034003cc

def z176 : W := mkw 0x1bffffff0fffefeb 0x06ffffffc3fffbfa 0xffffffff0fffffff 0xffffffffc3ffffff

def z177 : W := mkw 0x0000408c00240900 0x0000102300090240 0xec01c38c0c3c0f03 0x3b0070e3030f03c0

def z178 : W := mkw 0x13fffffaafdb66a8 0x04fffffeabf6d9aa 0xffffffffffffffff 0xffffffffffffffff

def z179 : W := mkw 0x0400408cc0241910 0xc100102330090644 0x0000000cc0000000 0x0000000330000000

def z180 : W := mkw 0x041cd1acc52c5b30 0xc107346b314b16cc 0x103dd02cc13c7031 0x840f740b304f1c0c

def z181 : W := mkw 0x0be322530a9284cb 0x02f8c894c2a4a132 0x03c2205302c380cc 0x40f08814c0b0e033

def z182 : W := mkw 0x023a9930a0000000 0x008ea64c28000000 0x103e1c30f0000000 0x840f870c3c000000

def z183 : W := mkw 0x841cd1add52cdb76 0xe107346b754b36dd 0xfc3dd3fffd3c7fff 0xbf0f74ffff4f1fff

def z184 : W := mkw 0x02ee03700f8006a8 0x00bb80dc03e001aa 0xbffc03800fc00ffc 0x2fff00e003f003ff

def z185 : W := mkw 0x1fffffefcffffff3 0xc7fffffbf3fffffc 0xffffffefcffffff3 0xfffffffbf3fffffc

def z186 : W := mkw 0x02ee03700f8006a8 0x00bb80dc03e001aa 0x9ffc03800c000700 0x27ff00e0030001c0

def z187 : W := mkw 0x0c5cd1adcf3edff3 0xc317346b73cfb7fc 0xfc3dd3accf3ffff3 0xbf0f74eb33cffffc

def z188 : W := mkw 0x13fffffaafdb6000 0x04fffffeabf6d800 0xfffffffffffff003 0xfffffffffffffc00

def z189 : W := mkw 0x1be36ecf0af7adc3 0x06f8dbb3c2bdeb70 0xefc3efcf0eff8fc3 0x7bf0fbf3c3bfe3f0

def z190 : W := mkw 0x03bbfbfaa0000000 0x00eefefea8000000 0x9bffdfb0f0000000 0xa6fff7ec3c000000

def z191 : W := mkw 0x02e202500a800488 0x00b8809402a00122 0x03c0000000000000 0x00f0000000000000

def z192 : W := mkw 0x83a32e577061b856 0xa0e8cb95dc186e15 0x63c23c7ff3e3f8ff 0xd8f08f1ffcf8fe3f

def z193 : W := mkw 0x014120000a120000 0x0050480002848000 0x87c1c0000c1c0000 0x21f0700003070000

def z194 : W := mkw 0x0000040000412000 0x0000010000104800 0x60023c7003e3f8ff 0xd8008f1c00f8fe3f

def z195 : W := mkw 0x0000040000412000 0x0000010000104800 0x2000000003e3f000 0x0800000000f8fc00

def z196 : W := mkw 0x07bbfbfee0241b30 0xc1eefeffb80906cc 0xdbfffffff0000f33 0xf6fffffffc0003cc

def z197 : W := mkw 0x136328000a920000 0x04d8ca0002a48000 0x03c0000000000000 0x00f0000000000000

def z198 : W := mkw 0x08c002450a368dc3 0x02300091428da370 0xefc003c00e3f8fc2 0x7bf000f0038fe3f0

def z199 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000204f00000003 0x50000813c0000000

def z200 : W := mkw 0x0000000000000000 0x0000000000000000 0xe401c0000c3c0001 0x39007000030f0000

def z201 : W := mkw 0x014120000a120000 0x0050480002848000 0x03c0200002038000 0x40f008000080e000

def z202 : W := mkw 0x0014900005084000 0x0005240001421000 0x943dc0000c1c0000 0x250f700003070000

def z203 : W := mkw 0x09c162cb0a1685c3 0x027058b2c285a170 0x8fc1e3c30e1f87c0 0x63f078f0c387e1f0

def z204 : W := mkw 0x0414d08cc52c5b30 0xc1053423314b16cc 0x2401d00ccd3c7f31 0x09007403334f1fcc

def z205 : W := mkw 0x800004055061b856 0xa000010154186e15 0x2000000003e3f8fc 0x0800000000f8fe3f

def z206 : W := mkw 0x8111fc8ff061b856 0xa0447f23fc186e15 0x0001fc0ff023f001 0x00007f03fc08fc00

def z207 : W := mkw 0x8000000050001014 0xa000000014000405 0x00000030f000003c 0x0000000c3c00000f

def z208 : W := mkw 0x0080024000000000 0x0020009000000000 0xcbc003c000000002 0x72f000f000000000

def z209 : W := mkw 0x0bef63fa0f9607a9 0x02fbd8fe83e581ea 0x9ffdc3800c1c0700 0x27ff70e0030701c0

def z210 : W := mkw 0x89c166cf5a77bdd7 0xa27059b3d69def75 0xefc1e3cf0fffffff 0x7bf078f3c3ffffff

def z211 : W := mkw 0x022e013005800228 0x008b804c0160008a 0xfc3e03b00dc00f3e 0xbf0f80ec037003cf

def z212 : W := mkw 0x040841a880040320 0x4102106a200100c8 0x0800038000000700 0x020000e0000001c0

def z213 : W := mkw 0x040841acc0241b30 0xc102106b300906cc 0x080003acc0000f32 0x020000eb300003cc

def z214 : W := mkw 0x0000000000000000 0x0000000000000000 0x6000200002238001 0x580008000088e000

def z215 : W := mkw 0x048843fcc0241fb8 0xc12210ff300907ee 0x080003fcc0000ffe 0x020000ff300003ff

def z216 : W := mkw 0x123e9d3005c96228 0x048fa74c0172588a 0x103e1c3001c0703c 0x840f870c00701c0f

def z217 : W := mkw 0x06fed3fccfac5fb8 0xc1bfb4ff33eb17ee 0xfffdd3accd3c7f33 0xbfff74eb334f1fcc

def z218 : W := mkw 0x0010900000000000 0x0004240000000000 0xd03dd00000000001 0xb40f740000000000

def z219 : W := mkw 0x13fffffaafdb6000 0x04fffffeabf6d800 0xffffff800ffff001 0xffffffe003fffc00

def z220 : W := mkw 0x03bbfbfee0201810 0x80eefeffb8080604 0xfbfffffff1207833 0xfefffffffc481e0c

def z221 : W := mkw 0x800004055061b856 0xa000010154186e15 0x00021c7ff1c078fe 0x8000871ffc701e3f

def z222 : W := mkw 0x09c122430a1284c3 0x02704890c284a130 0x03c02043020380c0 0x40f00810c080e030

def z223 : W := mkw 0x184404050fffedc3 0x0611010143fffb70 0x240000000fffffc0 0x0900000003fffff0

def z224 : W := mkw 0x888042cf50249dd7 0xa22010b3d4092775 0x080003fff0000ffe 0x020000fffc0003ff

def z225 : W := mkw 0x1373bc000adb6000 0x04dcef0002b6d800 0x03c3fc0002fff001 0x40f0ff0000bffc00

def z226 : W := mkw 0x00c002450a208cc2 0x0030009142882330 0xefc023cf0e238fc3 0x7bf008f3c388e3f0

def z227 : W := mkw 0x02e202500a800488 0x00b8809402a00122 0xefc203d00ec00fce 0x7bf080f403b003f3

def z228 : W := mkw 0x084400050fb68feb 0x0211000143eda3fa 0x240000000fff8ffc 0x0900000003ffe3ff

def z229 : W := mkw 0x0191facaa0000000 0x00647eb2a8000000 0xcbc1ffcff0000003 0x72f07ff3fc000000

def z230 : W := mkw 0x12fe9f700fc966a8 0x04bfa7dc03f259aa 0xfffe1ff00fc07ffe 0xffff87fc03f01fff

def z231 : W := mkw 0x0000000000000000 0x0000000000000000 0x40023c7ff0000003 0xd0008f1ffc000000

def z232 : W := mkw 0x09c162cf0a368dc3 0x027058b3c28da370 0xafc1c3800e3f8fc0 0x2bf070e0038fe3f0

def z233 : W := mkw 0x09d5f2cf0f3ecdc3 0x02757cb3c3cfb370 0xfffdf3cf0f3fffc3 0xffff7cf3c3cffff0

def z234 : W := mkw 0x0101608a00000000 0x0040582280000000 0x0001e00f00000001 0x00007803c0000000

def z235 : W := mkw 0x0000000000000000 0x0000000000000000 0x2000000003c008fc 0x0800000000f0023f

def z236 : W := mkw 0x0000000400240900 0x0000000100090240 0x240000000c3c0f00 0x09000000030f03c0

def z237 : W := mkw 0x13fffbfaaf9a4000 0x04fffefeabe69000 0xdffffffffc1c0003 0xf7ffffffff070000

def z238 : W := mkw 0x02ee03700f8006a8 0x00bb80dc03e001aa 0xdffe03f00c000702 0xf7ff80fc030001c0

def z239 : W := mkw 0x83bbfbfff0209856 0xa0eefefffc082615 0xdbfffffff00008ff 0xf6fffffffc00023f

def z240 : W := mkw 0x09c122470a368dc3 0x02704891c28da370 0x27c020430e3f8fc0 0x49f00810c38fe3f0

def z241 : W := mkw 0x82e206511ac1a4ce 0x20b8819446b06933 0x03c22c5332c380cc 0x40f08b14ccb0e033

def z242 : W := mkw 0x02ee03700f8006a8 0x00bb80dc03e001aa 0xfffc03c00e000fc2 0x7fff00f0038003f0

def z243 : W := mkw 0x09c562cf0fb68feb 0x027158b3c3eda3fa 0xefc1e3cf0fff8fff 0x7bf078f3c3ffe3ff

def z244 : W := mkw 0x09c162cf0a368dc3 0x027058b3c28da370 0x03c1e04f023f80c1 0x40f07813c08fe030

def z245 : W := mkw 0x13f7feca0fdb6000 0x04fdffb283f6d800 0xffffffcf0ffff003 0xfffffff3c3fffc00

def z246 : W := mkw 0x12220c0000c12000 0x0488830000304800 0x00020c0000c00000 0x0000830000300000

def z247 : W := mkw 0x004400000f8006a8 0x0011000003e001aa 0x040000000c000700 0x01000000030001c0

def z248 : W := mkw 0x04040004452c5b30 0xc1010001114b16cc 0x240000000d3c7f30 0x09000000034f1fcc

def z249 : W := mkw 0x808843fff0209856 0xa02210fffc082615 0x080003fff00008fe 0x020000fffc00023f

def z250 : W := mkw 0x03a36ada20000000 0x00e8dab688000000 0xcbc3efdf30000003 0x72f0fbf7cc000000

def z251 : W := mkw 0x17fffffccfff7fb8 0xc5ffffff33ffdfee 0xfffffffccfffffff 0xffffffff33ffffff

def z252 : W := mkw 0x09c162ca0a160581 0x027058b282858160 0xcfc1e3cf0c1c0703 0x73f078f3c30701c0

def z253 : W := mkw 0x008843faa0000000 0x002210fea8000000 0x48023ffff0000003 0xd2008ffffc000000

def z254 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000070000008fe 0x0000001c0000023f

def z255 : W := mkw 0x13ffbf700fdb66a8 0x04ffefdc03f6d9aa 0xffffff800ffff701 0xffffffe003fffdc0

def z256 : W := mkw 0x0bfbfbffaa368dc3 0x02fefeffea8da370 0xfffde3cf0e3f8fc3 0x7fff78f3c38fe3f0

def z257 : W := mkw 0x088042cf00248dc3 0x022010b3c0092370 0xec01c3cf0c3c0fc3 0x3b0070f3c30f03f0

def z258 : W := mkw 0x0333b80000000000 0x00ccee0000000000 0xd3fffc7ff0000003 0xf4ffff1ffc000000

def z259 : W := mkw 0x040841acc0241b30 0xc102106b300906cc 0x680013acc1207f33 0x9a0004eb30481fcc

def z260 : W := mkw 0x1115bc00055b6000 0x04456f000156d800 0xf43dfc000d3ff001 0xbd0f7f00034ffc00

def z261 : W := mkw 0x03bbfbfaa0000000 0x00eefefea8000000 0xdbffc3f000000002 0xf6fff0fc00000000

def z262 : W := mkw 0x09c122470a328cc3 0x02704891c28ca330 0x63c0204f022388c3 0x58f00813c088e230

def z263 : W := mkw 0x8088037550209efe 0xa02200dd540827bf 0x080003fff0000ffe 0x020000fffc0003ff

def z264 : W := mkw 0x840845add065bb76 0xe102116b74196edd 0x68023ffff3e3ffff 0xda008ffffcf8ffff

def z265 : W := mkw 0x0333b80000000000 0x00ccee0000000000 0x93fdc00000000000 0x24ff700000000000

def z266 : W := mkw 0x03ab2b7220000000 0x00eacadc88000000 0xdbfe2ff330000002 0xf6ff8bfccc000000

def z267 : W := mkw 0x823a9d35f061b856 0xa08ea74d7c186e15 0x703e3c7ff3e3f8ff 0xdc0f8f1ffcf8fe3f

def z268 : W := mkw 0x0000000100008042 0x0000000040002010 0x00002043020380c0 0x40000810c080e030

def z269 : W := mkw 0x0000000000000000 0x0000000000000000 0x4002007000000002 0xd000801c00000000

def z270 : W := mkw 0x1777fc8ccfff7910 0xc5ddff2333ffde44 0xf7fffc0ccffff001 0xfdffff0333fffc00

def z271 : W := mkw 0x04080120c0001230 0xc10200483000048c 0x00000020c0000030 0x000000083000000c

def z272 : W := mkw 0x177ff9accfbe5b30 0xc5dffe6b33ef96cc 0xfffdd3accd3c7f33 0xbfff74eb334f1fcc

def z273 : W := mkw 0x03bbfbfaa0000000 0x00eefefea8000000 0x9bfdc38000000000 0x26ff70e000000000

def z274 : W := mkw 0x800004055061b856 0xa000010154186e15 0x00003c0ff023f001 0x00000f03fc08fc00

def z275 : W := mkw 0x89c162cf5a369dd7 0xa27058b3d68da775 0xefc1e3fffe3f8fff 0x7bf078ffff8fe3ff

def z276 : W := mkw 0x09d1facfaa368dc3 0x02747eb3ea8da370 0xefc1ffcffe3f8fc3 0x7bf07ff3ff8fe3f0

def z277 : W := mkw 0x0000000000000000 0x0000000000000000 0x60000040020008c2 0x5800001000800230

def z278 : W := mkw 0x13632c000ad32000 0x04d8cb0002b4c800 0xe7c3ec000eff8001 0x79f0fb0003bfe000

def z279 : W := mkw 0x0000000440201810 0x8000000110080604 0x6002107cc3e078ff 0xd800841f30f81e3f

def z280 : W := mkw 0x098162cf00368dc3 0x026058b3c00da370 0x0801e3cf003f8fc3 0x020078f3c00fe3f0

def z281 : W := mkw 0x0337b80005084000 0x00cdee0001421000 0xf7fffc000d3c7001 0xfdffff00034f1c00

def z282 : W := mkw 0x0000000440201810 0x8000000110080604 0x2000000001207830 0x0800000000481e0c

def z283 : W := mkw 0x0418d1acc02c5910 0xc106346b300b1644 0xd83dd3acc03c7003 0xb60f74eb300f1c00

def z284 : W := mkw 0x80c006455a61bcd6 0xa030019156986f35 0xefc23fffffe3ffff 0xfbf08ffffff8ffff

def z285 : W := mkw 0x033bb930a0000000 0x00ceee4c28000000 0xd3fffc30f0000001 0xf4ffff0c3c000000

def z286 : W := mkw 0x0be362df0ab68dcb 0x02f8d8b7c2ada372 0xefc3e3df0eff8fcf 0x7bf0f8f7c3bfe3f3

def z287 : W := mkw 0x0141608c0a360900 0x00505823028d8240 0xefc1e38c0e3f8f03 0x7bf078e3038fe3c0

def z288 : W := mkw 0x83bbfffaf0413014 0xa0eefffebc104c05 0xdbfffffff1c0703f 0xf6fffffffc701c0f

def z289 : W := mkw 0x03b3fadaa0000000 0x00ecfeb6a8000000 0x03c3fc5ff0000001 0x40f0ff17fc000000

def z290 : W := mkw 0x0410d088800c4100 0x4104342220031040 0x0001c000001c0000 0x0000700000070000

def z291 : W := mkw 0x02e602400f800480 0x00b9809003e00120 0xfffe03c00fc00fc2 0xffff80f003f003f0

def z292 : W := mkw 0x004000000a120000 0x0010000002848000 0x240000000e3f8000 0x09000000038fe000

def z293 : W := mkw 0x03ef2b722f8006a8 0x00fbcadc8be001aa 0xfffe2ff33fc00ffe 0xffff8bfccff003ff

def z294 : W := mkw 0x02ee03700f8006a8 0x00bb80dc03e001aa 0xfffe3fffffc00fff 0xffff8ffffff003ff

def z295 : W := mkw 0x82ee07705fc136bc 0xa0bb81dc17f04daf 0xfffe1ff0ffc07ffe 0xffff87fc3ff01fff

def z296 : W := mkw 0x026e01200f800220 0x009b804803e00088 0xfffe03a00fc00f32 0xffff80e803f003cc

def z297 : W := mkw 0x8410d48dd06df956 0xe1043523741b7e55 0x6003fc7ff3fff8ff 0xd800ff1ffcfffe3f

def z298 : W := mkw 0x03bbbb72a0000000 0x00eeeedca8000000 0x13fe3c73f0000000 0xc4ff8f1cfc000000

def z299 : W := mkw 0x0000040440613810 0x8000010110184e04 0x60023c2cc3e3f833 0xd8008f0b30f8fe0c

def z300 : W := mkw 0x0014d08c052c4900 0x00053423014b1240 0xfc3dd38c0d3c7f03 0xbf0f74e3034f1fc0

def z301 : W := mkw 0x02bad3f880000000 0x00aeb4fe20000000 0xdbffd3fcc0000003 0xf6fff4ff30000000

def z302 : W := mkw 0x86fed7fddfedfffe 0xe1bfb5ff77fb7fff 0xffffffffffffffff 0xffffffffffffffff

def z303 : W := mkw 0x041cd1acc52c5b30 0xc107346b314b16cc 0xfc3ffffffd3c7f33 0xff0fffffff4f1fcc

def z304 : W := mkw 0x0000408800040100 0x0000102200010040 0x8c01c3800c1c0700 0x230070e0030701c0

def z305 : W := mkw 0x177ff9a88f9e4320 0x45dffe6a23e790c8 0x9ffdc3800c1c0700 0x27ff70e0030701c0

def z306 : W := mkw 0x13632c000ad32000 0x04d8cb0002b4c800 0x63c23c0003e3f001 0xd8f08f0000f8fc00

def z307 : W := mkw 0x09cd63ef0f368fe3 0x027358fbc3cda3f8 0xfffde3ef0f3f8ff3 0xffff78fbc3cfe3fc

def z308 : W := mkw 0x041cd1ac852c4b20 0x4107346b214b12c8 0xfc3dc38c0c3c0f03 0x3f0f70e3030f03c0

def z309 : W := mkw 0x041cd1a8850c4320 0x4107346a214310c8 0xfc3dd3800d3c7701 0xbf0f74e0034f1dc0

def z310 : W := mkw 0x02ae037005800228 0x00ab80dc0160008a 0xdbfe03f001c0003e 0xf6ff80fc0070000f

def z311 : W := mkw 0x0010d08880000000 0x0004342220000000 0x0001d00cc0000001 0x0000740330000000

def z312 : W := mkw 0x055df1accf3e5b30 0xc1577c6b33cf96cc 0xfffdf3accf3fff33 0xffff7ceb33cfffcc

def z313 : W := mkw 0x041cd1a8c5085230 0xc107346a3142148c 0xd83dd3acc1007033 0xb60f74eb30401c0c

def z314 : W := mkw 0x0004000005800228 0x000100000160008a 0x0000000001c0003c 0x000000000070000f

def z315 : W := mkw 0x008042ca00000000 0x002010b280000000 0x080003cf00000002 0x020000f3c0000000

def z316 : W := mkw 0x0bbbfbffa0368943 0x02eefeffe80da250 0xdbfffffff03f8003 0xf6fffffffc0fe000

def z317 : W := mkw 0x0000040000412000 0x0000010000104800 0x00003c000023f001 0x00000f000008fc00

def z318 : W := mkw 0x12369c0005c96000 0x048da70001725800 0xf43fdc000dfc7001 0xbd0ff700037f1c00

def z319 : W := mkw 0x841c9520d5497234 0xe107254835525c8d 0x103e1c30f1c0703c 0x840f870c3c701c0f

def z320 : W := mkw 0x018963faa0000000 0x006258fea8000000 0xcbc1e3fff0000003 0x72f078fffc000000

def z321 : W := mkw 0x19c566cf0fffedc3 0x067159b3c3fffb70 0xefc1e3cf0fffffc3 0x7bf078f3c3fffff0

def z322 : W := mkw 0x03bbfbfea0240900 0x00eefeffa8090240 0xfffffffffc3c0f03 0xffffffffff0f03c0

def z323 : W := mkw 0x014124000a532000 0x005049000294c800 0xe7c3fc000ffff001 0xf9f0ff0003fffc00

def z324 : W := mkw 0x0014940005496000 0x0005250001525800 0xf43ffc000ffff001 0xfd0fff0003fffc00

def z325 : W := mkw 0x82aa07755061b856 0xa0aa81dd54186e15 0xfbfe3ffff3e3f8ff 0xfeff8ffffcf8fe3f

def z326 : W := mkw 0x07bffbfaa50c4320 0x41effefea94310c8 0x9ffdc3800c1c0700 0x27ff70e0030701c0

def z327 : W := mkw 0x89c126431a53a4c7 0x22704990c694e931 0x03c22c5332c380cc 0x40f08b14ccb0e033

def z328 : W := mkw 0x10109c0000496000 0x0404270000125800 0x00001c0000007000 0x0000070000001c00

def z329 : W := mkw 0x151dfdacc57f7b30 0xc5477f6b315fdecc 0xfc3dffaccd3fff33 0xbf0f7feb334fffcc

def z330 : W := mkw 0x03ef23700f9206a8 0x00fbc8dc03e481aa 0xffffe3f00fff8fff 0xfffff8fc03ffe3ff

def z331 : W := mkw 0x8000040050413014 0xa000010014104c05 0x60023c30f3e3f03d 0xd8008f0c3cf8fc0f

def z332 : W := mkw 0x137fbd200fdb6220 0x04dfef4803f6d888 0xffffffa00fffff33 0xffffffe803ffffcc

def z333 : W := mkw 0x04149004452c5b30 0xc1052401114b16cc 0xf43dd0000d3c7f31 0xbd0f7400034f1fcc

def z334 : W := mkw 0x0beb63ff0a368dc3 0x02fad8ffc28da370 0xffffe3ff0e3f8fc3 0xfffff8ffc38fe3f0

def z335 : W := mkw 0x073ff9acc52c5b30 0xc1cffe6b314b16cc 0xffffffaccd3c7f33 0xffffffeb334f1fcc

def z336 : W := mkw 0x02aa037000000000 0x00aa80dc00000000 0x9bfc038000000000 0x26ff00e000000000

def z337 : W := mkw 0x800c05255561ba76 0xa003014955586e9d 0xfc3e3fffffe3ffff 0xff0f8ffffff8ffff

def z338 : W := mkw 0x0901608a00160101 0x0240582280058040 0x0001c000001c0000 0x0000700000070000

def z339 : W := mkw 0x040c41acc52c5b30 0xc103106b314b16cc 0x2c0003accd3c7f32 0x0b0000eb334f1fcc

def z340 : W := mkw 0x041cd1a8c50c5330 0xc107346a314314cc 0x9c3dd3a0cd1c7730 0xa70f74e833471dcc

def z341 : W := mkw 0x001cd1a885084000 0x0007346a21421000 0xfc3dd3accd3c7003 0xbf0f74eb334f1c00

def z342 : W := mkw 0x144404044fff7b30 0xc511010113ffdecc 0x240000000fffff30 0x0900000003ffffcc

def z343 : W := mkw 0x0080025000000488 0x0020009400000122 0x00000050000000cc 0x0000001400000033

def z344 : W := mkw 0x06ee03744fac5fb8 0xc1bb80dd13eb17ee 0xfffe03f00ffc7ffe 0xffff80fc03ff1fff

def z345 : W := mkw 0x0000000440201810 0x8000000110080604 0x0000002cc0000832 0x0000000b3000020c

def z346 : W := mkw 0x0000408c00240900 0x0000102300090240 0x0001c00c003c0001 0x00007003000f0000

def z347 : W := mkw 0x840841add0249b76 0xe102106b740926dd 0x080003fff0000ffe 0x020000fffc0003ff

def z348 : W := mkw 0x8000000550209856 0xa000000154082615 0x6000207ff22388ff 0x5800081ffc88e23f

def z349 : W := mkw 0x82e206555ae1bcde 0xa0b8819556b86f37 0x63c23c7ff3e3f8ff 0xd8f08f1ffcf8fe3f

def z350 : W := mkw 0x06fed3f88f8c47a8 0x41bfb4fe23e311ea 0xffffc3f00fdc0ffe 0xfffff0fc03f703ff

def z351 : W := mkw 0x0008013000000228 0x0002004c0000008a 0x000000300000003c 0x0000000c0000000f

def z352 : W := mkw 0x145cd5accfff7b30 0xc517356b33ffdecc 0xfc3dd3accfffff33 0xbf0f74eb33ffffcc

def z353 : W := mkw 0x018162cf00208842 0x006058b3c0082210 0xebc1e3cf022388c3 0x7af078f3c088e230

def z354 : W := mkw 0x04dcd3eccf2c5fb0 0xc13734fb33cb17ec 0xfffdd3eccf3c7ff3 0xffff74fb33cf1ffc

def z355 : W := mkw 0x1151bc000a5b6000 0x04546f000296d800 0xe7c1fc000e3ff001 0x79f07f00038ffc00

def z356 : W := mkw 0x8000000550209856 0xa000000154082615 0x6002007ff3c008fe 0xd800801ffcf0023f

def z357 : W := mkw 0x004400000f800000 0x0011000003e00000 0x240000000fc00000 0x0900000003f00000

def z358 : W := mkw 0x1377bc000fdb66a8 0x04ddef0003f6d9aa 0xf7fffc000ffffffd 0xfdffff0003ffffff

def z359 : W := mkw 0x804404055fe1befe 0xa011010157f86fbf 0x64023c7fffe3ffff 0xd9008f1ffff8ffff

def z360 : W := mkw 0x03bffbfaa5000220 0x00effefea9400088 0xfffffffffd000f33 0xffffffffff4003cc

def z361 : W := mkw 0x163e9d20c5c97230 0xc58fa74831725c8c 0x103e1c20c1c07030 0x840f870830701c0c

def z362 : W := mkw 0x0dddf3eecf3e5fb1 0xc3777cfbb3cf97ec 0xfffdd3accd3c7f33 0xbfff74eb334f1fcc

def z363 : W := mkw 0x0004000005000220 0x0001000001400088 0x240000000d000f30 0x09000000034003cc

def z364 : W := mkw 0x13f7be500fdb6488 0x04fdef9403f6d922 0xf7fffc500ffff0cd 0xfdffff1403fffc33

def z365 : W := mkw 0x023a9930a0000000 0x008ea64c28000000 0x103c000000000000 0x040f000000000000

def z366 : W := mkw 0x0000000040001010 0x8000000010000404 0x00001020c1007030 0x8000040830401c0c

def z367 : W := mkw 0x02ee03700f8006a8 0x00bb80dc03e001aa 0x9ffe03b00dc0073c 0xa7ff80ec037001cf

def z368 : W := mkw 0x800004011041a046 0x2000010044106811 0x60022c7333c388fe 0xd8008b1cccf0e23f

def z369 : W := mkw 0x0901608f00368943 0x02405823c00da250 0xec01e38f0c3f8f03 0x3b0078e3c30fe3c0

def z370 : W := mkw 0x0199f3ea80000000 0x00667cfaa0000000 0xdbfdf3efc0000003 0xf6ff7cfbf0000000

def z371 : W := mkw 0x06ee43fccfa41fb8 0xc1bb90ff33e907ee 0xfffe03fccfc00ffe 0xffff80ff33f003ff

def z372 : W := mkw 0x0800000500368943 0x02000001400da250 0x00000000003f8000 0x00000000000fe000

def z373 : W := mkw 0x800004011041a046 0x2000010044106811 0x00002c0330038000 0x00000b00cc00e000

def z374 : W := mkw 0x09c162cf0a368dc3 0x027058b3c28da370 0xefc3e3ff0fff8fff 0xfbf0f8ffc3ffe3ff

def z375 : W := mkw 0x03fffbfaaf8006a8 0x00fffefeabe001aa 0xdffffffffc000703 0xf7ffffffff0001c0

def z376 : W := mkw 0x801494055569f856 0xa0052501555a7e15 0xf43ffc7ffffff8ff 0xfd0fff1ffffffe3f

def z377 : W := mkw 0x088042cf00248dc3 0x022010b3c0092370 0x680023cf02238fc3 0x5a0008f3c088e3f0

def z378 : W := mkw 0x0181224200000000 0x0060489080000000 0x03c0204300000000 0x40f00810c0000000

def z379 : W := mkw 0x800004015041b056 0xa000010054106c15 0x00023c73f3c3f0fc 0xc0008f1cfcf0fc3f

def z380 : W := mkw 0x000c012005000220 0x0003004801400088 0x9c3c03800c000700 0x270f00e0030001c0

def z381 : W := mkw 0x09c122430a1284c3 0x02704890c284a130 0xefc023c30e038fc2 0x7bf008f0c380e3f0

def z382 : W := mkw 0x02aa43faa0000000 0x00aa90fea8000000 0xdbfe03fff0000002 0xf6ff80fffc000000

def z383 : W := mkw 0x12ee07700fdb66a8 0x04bb81dc03f6d9aa 0xfffe03f00ffffffe 0xffff80fc03ffffff

def z384 : W := mkw 0x0000000440201810 0x8000000110080604 0x0000100cc0207001 0x0000040330081c00

def z385 : W := mkw 0x1377bc000fdb6000 0x04ddef0003f6d800 0xb7fdc0000ffff000 0x2dff700003fffc00

def z386 : W := mkw 0x8dddf7efdf7ffff7 0xe3777dfbf7dffffd 0xffffffffffffffff 0xffffffffffffffff

def z387 : W := mkw 0x02ee03700f8006a8 0x00bb80dc03e001aa 0xfffe03800fc00700 0xffff80e003f001c0

def z388 : W := mkw 0x0901200300128043 0x02404800c004a010 0x0000200300038000 0x00000800c000e000

def z389 : W := mkw 0x0010900000084000 0x0004240000021000 0x0001d000003c7001 0x00007400000f1c00

def z390 : W := mkw 0x09c162cb0a1284c3 0x027058b2c284a130 0xcbc1e3cf020380c3 0x72f078f3c080e030

def z391 : W := mkw 0x094120050a368dc3 0x02504801428da370 0xe7c1e0000e3f8fc1 0x79f07800038fe3f0

def z392 : W := mkw 0x0bef23730f9286eb 0x02fbc8dcc3e4a1ba 0xfffe23f30fc38ffe 0xffff88fcc3f0e3ff

def z393 : W := mkw 0x0018d1a880000000 0x0006346a20000000 0xd83ffffff0000003 0xf60ffffffc000000

def z394 : W := mkw 0x03b3faca00000000 0x00ecfeb280000000 0xdbffffcf00000003 0xf6fffff3c0000000

def z395 : W := mkw 0x063ed1bcc5ac5b38 0xc18fb46f316b16ce 0xfc3fd3bccdfc7f3f 0xbf0ff4ef337f1fcf

def z396 : W := mkw 0x0ffffbffef3edff3 0xc3fffefffbcfb7fc 0xffffffffff3ffff3 0xffffffffffcffffc

def z397 : W := mkw 0x02aa037000000000 0x00aa80dc00000000 0xfbfe03f003c008fe 0xfeff80fc00f0023f

def z398 : W := mkw 0x0000408aa0000000 0x00001022a8000000 0x0000000ff0000000 0x00000003fc000000

def z399 : W := mkw 0x0000000000000000 0x0000000000000000 0x00022c5330000000 0x40008b14cc000000

def z400 : W := mkw 0x03a32a5220000000 0x00e8ca9488000000 0x43c23c7ff0000003 0xd0f08f1ffc000000

def z401 : W := mkw 0x1911fc8f007fe943 0x06447f23c01ffa50 0x0001fc0f003ff001 0x00007f03c00ffc00

def z402 : W := mkw 0x0000000000000000 0x0000000000000000 0x0002003001c0003c 0x8000800c0070000f

def z403 : W := mkw 0x0018d1ac80240900 0x0006346b20090240 0xfc3dd3accc3c0f03 0xbf0f74eb330f03c0

def z404 : W := mkw 0x0dc562cf4f3edff3 0xc37158b3d3cfb7fc 0xefc1e3cf0f3ffff3 0x7bf078f3c3cffffc

def z405 : W := mkw 0x0000000500208842 0x0000000140082210 0x60023c7ff22388c3 0xd8008f1ffc88e230

def z406 : W := mkw 0x0155b0000f1a4000 0x00556c0003c69000 0xf7fdf0000f3ff001 0xfdff7c0003cffc00

def z407 : W := mkw 0x0111b80000000000 0x00446e0000000000 0x0001fc0000000001 0x00007f0000000000

def z408 : W := mkw 0x8111fc8ff061b856 0xa0447f23fc186e15 0x6003fc7ff3e3f8ff 0xd800ff1ffcf8fe3f

def z409 : W := mkw 0x06fe9370cf8856b8 0xc1bfa4dc33e215ae 0xfffe13f0cfc07ffe 0xffff84fc33f01fff

def z410 : W := mkw 0x041cd1acc52c5b30 0xc107346b314b16cc 0x183c13acc1007f32 0x860f04eb30401fcc

def z411 : W := mkw 0x0bfffbffafb68feb 0x02fffeffebeda3fa 0xffffffffffff8fff 0xffffffffffffe3ff

def z412 : W := mkw 0x83ffffffffe1befe 0xa0fffffffff86fbf 0xffffffffffe3ffff 0xfffffffffff8ffff

def z413 : W := mkw 0x12769c000fc96000 0x049da70003f25800 0xf7fe1c000fc07000 0xfdff870003f01c00

def z414 : W := mkw 0x063e9130c5885238 0xc18fa44c3162148e 0x103e1030c1c0703c 0x840f840c30701c0f

def z415 : W := mkw 0x03bbfbfaa0000000 0x00eefefea8000000 0xdbfde3cf00000003 0x76ff78f3c0000000

def z416 : W := mkw 0x0222081020000000 0x0088820408000000 0x00020c1030000000 0x000083040c000000

def z417 : W := mkw 0x884004055a77bdd7 0xa2100101569def75 0x64023c7fffffffff 0xd9008f1fffffffff

def z418 : W := mkw 0x0bf3facf0a368dc3 0x02fcfeb3c28da370 0xffffffcf0e3f8fc3 0xfffffff3c38fe3f0

def z419 : W := mkw 0x04040000050c4320 0x41010000014310c8 0x040000000c1c0700 0x01000000030701c0

def z420 : W := mkw 0x02ee43fc0fa40fa8 0x00bb90ff03e903ea 0xffffc3fc0ffc0fff 0xfffff0ff03ff03ff

def z421 : W := mkw 0x8901648f5077b957 0xa2405923d41dee55 0x0001fc0ff03ff001 0x00007f03fc0ffc00

def z422 : W := mkw 0x000c012005000220 0x0003004801400088 0x103c002001000030 0x840f00080040000c

def z423 : W := mkw 0x822e053555e1ba7e 0xa08b814d55786e9f 0x703e3c7ff3e3f8ff 0xdc0f8f1ffcf8fe3f

def z424 : W := mkw 0x0000000000000000 0x0000000000000000 0x6002000003c00000 0xd800800000f00000

def z425 : W := mkw 0x0080025220000000 0x0020009488000000 0x0000005330000000 0x00000014cc000000

def z426 : W := mkw 0x041c912085084220 0x4107244821421088 0x103c000000000000 0x040f000000000000

def z427 : W := mkw 0x03ab63fa00000000 0x00ead8fe80000000 0xdbffe3ff00000003 0xf6fff8ffc0000000

def z428 : W := mkw 0x018162ca00000000 0x006058b280000000 0xcbc3fffff0000003 0xf2f0fffffc000000

def z429 : W := mkw 0x12369c0005c96000 0x048da70001725800 0x703e3c0003e3f001 0xdc0f8f0000f8fc00

def z430 : W := mkw 0x841cd5add56dfb76 0xe107356b755b7edd 0xfc3dd3accfffffff 0xbf0f74eb33ffffff

def z431 : W := mkw 0x041cd1a8850c4320 0x4107346a214310c8 0xdc3dd3accc1c0703 0xb70f74eb330701c0

def z432 : W := mkw 0x0c8843efc0249ff3 0xc32210fbf00927fc 0x080003efc0000ff2 0x020000fbf00003fc

def z433 : W := mkw 0x9111bc05507bf856 0xa4446f01541efe15 0x0001fc0ff03ff001 0x00007f03fc0ffc00

def z434 : W := mkw 0x048843fee0241b30 0xc12210ffb80906cc 0x080003fff0000f32 0x020000fffc0003cc

def z435 : W := mkw 0x177ffda88fdf6320 0x45dfff6a23f7d8c8 0xffffff800ffff701 0xffffffe003fffdc0

def z436 : W := mkw 0x00c002400a000480 0x0030009002800120 0x03c00040020000c0 0x40f0001000800030

def z437 : W := mkw 0x026e01300f8006a8 0x009b804c03e001aa 0x343e00300fc00ffc 0x8d0f800c03f003ff

def z438 : W := mkw 0x06fed3f88f8c47a8 0x41bfb4fe23e311ea 0x9ffdc3800c1c0700 0x27ff70e0030701c0

def z439 : W := mkw 0x800004055061b856 0xa000010154186e15 0x00022c7ff2c388fe 0x40008b1ffcb0e23f

def z440 : W := mkw 0x0018d1acc0201810 0x8006346b30080604 0xf83dd3acc1207833 0xbe0f74eb30481e0c

def z441 : W := mkw 0x08800243000084c3 0x02200090c0002130 0x00000043000000c0 0x00000010c0000030

def z442 : W := mkw 0x89c126475a73bcd7 0xa2704991d69cef35 0x63c23c7ff3e3f8ff 0xd8f08f1ffcf8fe3f

def z443 : W := mkw 0x000c012005000220 0x0003004801400088 0xfc3e03f00fc00ffe 0xff0f80fc03f003ff

def z444 : W := mkw 0x03bbfffaa0412000 0x00eefffea8104800 0xfbfffffff3e3f003 0xfefffffffcf8fc00

def z445 : W := mkw 0x07bbfbfee02c5910 0xc1eefeffb80b1644 0xdbfffffff03c7003 0xf6fffffffc0f1c00

def z446 : W := mkw 0x09c963ff0a368feb 0x027258ffc28da3fa 0xefc1e3ff0e3f8fff 0x7bf078ffc38fe3ff

def z447 : W := mkw 0x09d9f3ef8a368dc3 0x02767cfbe28da370 0xfffdf3efce3f8fc3 0xffff7cfbf38fe3f0

def z448 : W := mkw 0x12769c000fdb6000 0x049da70003f6d800 0x343e1c000ffff000 0x8d0f870003fffc00

def z449 : W := mkw 0x137fbd30afdb6000 0x04dfef4c2bf6d800 0xf7fffc30fffff001 0xfdffff0c3ffffc00

def z450 : W := mkw 0x814124055a73b856 0xa0504901569cee15 0xe7c3fc7ffffff8ff 0xf9f0ff1ffffffe3f

def z451 : W := mkw 0x0dc963efca369ff3 0xc37258fbf28da7fc 0xefc1e3efce3f8ff3 0x7bf078fbf38fe3fc

def z452 : W := mkw 0x82ee07711fc1a6ee 0x20bb81dc47f069bb 0xfffe2ff33fc38ffe 0xffff8bfccff0e3ff

def z453 : W := mkw 0x02ee07700fc126a8 0x00bb81dc03f049aa 0xfffe3ff00fe3ffff 0xffff8ffc03f8ffff

def z454 : W := mkw 0x0111f88aa0000000 0x00447e22a8000000 0x4003fc7ff0000003 0xd000ff1ffc000000

def z455 : W := mkw 0x02fe9b70af8006a8 0x00bfa6dc2be001aa 0xfffe1ff0ffc00ffe 0xffff87fc3ff003ff

def z456 : W := mkw 0x00cc03700f8006a8 0x003300dc03e001aa 0x2c0003f00fc00ffe 0x0b0000fc03f003ff

def z457 : W := mkw 0x1377b8000f9a4000 0x04ddee0003e69000 0xf7fdd0000d3c7001 0xbdff7400034f1c00

def z458 : W := mkw 0x08c042cf0a248dc3 0x023010b3c2892370 0xefc003cf0e000fc2 0x7bf000f3c38003f0

def z459 : W := mkw 0x04040004452c5b30 0xc1010001114b16cc 0x6400102ccd3c7f33 0x9900040b334f1fcc

def z460 : W := mkw 0x07fffbfeefac5fb8 0xc1fffeffbbeb17ee 0xfffffffffffc7fff 0xffffffffffff1fff

def z461 : W := mkw 0x098162cf00368943 0x026058b3c00da250 0xcbc1e3cf003f8003 0x72f078f3c00fe000

def z462 : W := mkw 0x800004055061b856 0xa000010154186e15 0x60003c4ff223f8c3 0x58000f13fc88fe30

def z463 : W := mkw 0x1373bc000ad32000 0x04dcef0002b4c800 0xd3fffc0002c38001 0xf4ffff0000b0e000

def z464 : W := mkw 0x041c9124c5285a30 0xc1072449314a168c 0x703c102cc1207833 0x9c0f040b30481e0c

def z465 : W := mkw 0x0800408f00248943 0x02001023c0092250 0x0000000f00000000 0x00000003c0000000

def z466 : W := mkw 0x03bbfbffa0208842 0x00eefeffe8082210 0xfbfffffff22388c3 0xfefffffffc88e230

def z467 : W := mkw 0x0410d08cc02c5910 0xc1043423300b1644 0xec01d38ccc3c7f03 0x3b0074e3330f1fc0

def z468 : W := mkw 0x137ffda88fdb6000 0x04dfff6a23f6d800 0xffffffaccffff003 0xffffffeb33fffc00

def z469 : W := mkw 0x9377bc055ffbf856 0xa4ddef0157fefe15 0xf7fffc000ffff8fd 0xfdffff0003fffe3f

def z470 : W := mkw 0x0222001000800008 0x0088800400200002 0x0002001000c0000c 0x0000800400300003

def z471 : W := mkw 0x02fe93700f8846a8 0x00bfa4dc03e211aa 0xffffd3f00ffc7fff 0xfffff4fc03ff1fff

def z472 : W := mkw 0x13ef2f700fd326a8 0x04fbcbdc03f4c9aa 0xfffe2ff00fc38ffe 0xffff8bfc03f0e3ff

def z473 : W := mkw 0x09c162ce0a360d81 0x027058b3828d8360 0xefc1c38c0c3c0f03 0x3bf070e3030f03c0

def z474 : W := mkw 0x040c0124452c5b30 0xc1030049114b16cc 0xfc3c03a00d3c7f32 0xbf0f00e8034f1fcc

def z475 : W := mkw 0x03bffbfaa5800228 0x00effefea960008a 0xdbfffffff1c0003f 0xf6fffffffc70000f

def z476 : W := mkw 0x01c162ca0a000480 0x007058b282800120 0xefc1e3cf0e000fc3 0x7bf078f3c38003f0

def z477 : W := mkw 0x0232980000000000 0x008ca60000000000 0x103e1c0000000000 0x840f870000000000

def z478 : W := mkw 0x0418d1acc02c5b30 0xc106346b300b16cc 0x0801d3acc03c7f33 0x020074eb300f1fcc

def z479 : W := mkw 0x800004055061b856 0xa000010154186e15 0x60023c0003e3f8fd 0xd8008f0000f8fe3f

def z480 : W := mkw 0x03fbfbfaaa000480 0x00fefefeaa800120 0xfffffffffe000fc3 0xffffffffff8003f0

def z481 : W := mkw 0x03ab6bfaa0000000 0x00eadafea8000000 0x0bc22ffff0000002 0x42f08bfffc000000

def z482 : W := mkw 0x09c162cf0a368dc3 0x027058b3c28da370 0x0bc023cf02038fc2 0x42f008f3c080e3f0

def z483 : W := mkw 0x09c162cf0a368dc3 0x027058b3c28da370 0x8fc1e38f0c3f8701 0x23f078e3c30fe1c0

def z484 : W := mkw 0x8000040050413014 0xa000010014104c05 0x60021c70f3c078fe 0xd800871c3cf01e3f

def z485 : W := mkw 0x09c122420a120481 0x0270489082848120 0x03c0000000000000 0x00f0000000000000

def z486 : W := mkw 0x13ffbf700fdb6000 0x04ffefdc03f6d800 0xfffffff00ffff003 0xfffffffc03fffc00

def z487 : W := mkw 0x0004000005000000 0x0001000001400000 0xf43c00000d000000 0xbd0f000003400000

def z488 : W := mkw 0x008843faa00006a8 0x002210fea80001aa 0x080003fff0000ffe 0x020000fffc0003ff

def z489 : W := mkw 0x8000040050413014 0xa000010014104c05 0x00001c00f0007000 0x000007003c001c00

def z490 : W := mkw 0x0101280220000000 0x00404a0088000000 0x00002c0330000000 0x00000b00cc000000

def z491 : W := mkw 0x800004055061b856 0xa000010154186e15 0x60023c0ff3e3f001 0xd8008f03fcf8fc00

def z492 : W := mkw 0x8000000550209856 0xa000000154082615 0x40023c7ff00008ff 0xd0008f1ffc00023f

def z493 : W := mkw 0x03fffbfaaf8006a8 0x00fffefeabe001aa 0xffffc3f00fc00ffe 0xfffff0fc03f003ff

def z494 : W := mkw 0x0000000540209852 0x8000000150082614 0x6000306fc323f8f3 0xd8000c1bf0c8fe3c

def z495 : W := mkw 0x0aee43ff0fa48feb 0x02bb90ffc3e923fa 0xfffe03ff0fc00ffe 0xffff80ffc3f003ff

def z496 : W := mkw 0x884004055a77bdd7 0xa2100101569def75 0x240000000ffffffc 0x0900000003ffffff

def z497 : W := mkw 0x014120050a328842 0x00504801428ca210 0xe7c1e04f0e3f88c3 0x79f07813c38fe230

def z498 : W := mkw 0x10000400005b6000 0x040001000016d800 0x00000000003ff000 0x00000000000ffc00

def z499 : W := mkw 0x0911f88fa0368943 0x02447e23e80da250 0x0001fc0ff03f8001 0x00007f03fc0fe000

def z500 : W := mkw 0x02ee03744fa01eb8 0x80bb80dd13e807ae 0xfffe13fccfe07fff 0xffff84ff33f81fff

def z501 : W := mkw 0x03fbfbfaaa120000 0x00fefefeaa848000 0xfffffffffe3f8003 0xffffffffff8fe000

def z502 : W := mkw 0x1236980005884000 0x048da60001621000 0x103c000000000000 0x040f000000000000

def z503 : W := mkw 0x0410d08cc02c5910 0xc1043423300b1644 0x6001d02cc13c7833 0x9800740b304f1e0c

def z504 : W := mkw 0x1b77bc050fffedc3 0x06ddef0143fffb70 0xf7fffc000fffffc1 0xfdffff0003fffff0

def z505 : W := mkw 0x13672c000fdb6000 0x04d9cb0003f6d800 0x27c22c000ffff000 0x49f08b0003fffc00

def z506 : W := mkw 0x004000000a000000 0x0010000002800000 0xe7c000000e000000 0x79f0000003800000

def z507 : W := mkw 0x004c01200f8006a8 0x0013004803e001aa 0xfc3c03a00fc00ffe 0xbf0f00e803f003ff

def z508 : W := mkw 0x00880370000006a8 0x002200dc000001aa 0x680203f003c00ffe 0xda0080fc00f003ff

def z509 : W := mkw 0x0ffff3ffcfbedffb 0xc3fffcfff3efb7fe 0xfffff3ffcfffffff 0xfffffcfff3ffffff

def z510 : W := mkw 0x03bbbb7000000000 0x00eeeedc00000000 0xdbfffff000000003 0xf6fffffc00000000

def z511 : W := mkw 0x800004055061b856 0xa000010154186e15 0x60003c2ff123f833 0x98000f0bfc48fe0c

def z512 : W := mkw 0x800004055061b856 0xa000010154186e15 0x20022c5333e3f8fc 0x48008b14ccf8fe3f

def z513 : W := mkw 0x09c162cf0a368dc3 0x027058b3c28da370 0x8fc1c3cf0c1c0fc2 0x23f070f3c30703f0

def z514 : W := mkw 0x92369c0055c97014 0xa48da70015725c05 0x103e1c30f1c0703c 0x840f870c3c701c0f

def z515 : W := mkw 0x0080024000000480 0x0020009000000120 0x080003c000000fc2 0x020000f0000003f0

def z516 : W := mkw 0x0000000500208842 0x0000000140082210 0x6002207f03e388ff 0xd800881fc0f8e23f

def z517 : W := mkw 0x8000000550209856 0xa000000154082615 0x00000000000008fc 0x000000000000023f

def z518 : W := mkw 0x1377b8000f9a4000 0x04ddee0003e69000 0xf7fde0000e3f8001 0x7dff7800038fe000

def z519 : W := mkw 0x02ee03700f800000 0x00bb80dc03e00000 0xfffe03f00fc00002 0xffff80fc03f00000

def z520 : W := mkw 0x044400044fac5fb8 0xc111000113eb17ee 0x240000000ffc7ffc 0x0900000003ff1fff

def z521 : W := mkw 0x0226000005800000 0x0089800001600000 0x103e000001c00000 0x840f800000700000

def z522 : W := mkw 0x826604055fe1b856 0xa099810157f86e15 0xf7fe3c7fffe3f8ff 0xfdff8f1ffff8fe3f

def z523 : W := mkw 0x02ee03700f8006a8 0x00bb80dc03e001aa 0x13fe007003c000fc 0xc4ff801c00f0003f

def z524 : W := mkw 0x0dddf3ef8f3ecfe3 0x43777cfbe3cfb3f8 0xfffde3cf0e3f8fc3 0x7fff78f3c38fe3f0

def z525 : W := mkw 0x0000040000412000 0x0000010000104800 0x00021c0001c07000 0x8000870000701c00

def z526 : W := mkw 0x0008012000000220 0x0002004800000088 0x080003a000000f32 0x020000e8000003cc

def z527 : W := mkw 0x1111bc00005b6000 0x04446f000016d800 0x6003fc0003fff001 0xd800ff0000fffc00

def z528 : W := mkw 0x8000040050413014 0xa000010014104c05 0x40023c7ff1c0703f 0xd0008f1ffc701c0f

def z529 : W := mkw 0x0000408c40241910 0x8000102310090644 0xec01d3accd3c7f33 0xbb0074eb334f1fcc

def z530 : W := mkw 0x02ae037005000220 0x00ab80dc01400088 0xfffe03f00d000f32 0xffff80fc034003cc

def z531 : W := mkw 0x8018d5add061b856 0xa006356b74186e15 0xf83ffffff3e3f8ff 0xfe0ffffffcf8fe3f

def z532 : W := mkw 0x0bfbfbfaaa160581 0x02fefefeaa858160 0x9ffdc3800c1c0700 0x27ff70e0030701c0

def z533 : W := mkw 0x0000000000000000 0x0000000000000000 0x40023c0000000001 0xd0008f0000000000

def z534 : W := mkw 0x001cd1a885000220 0x0007346a21400088 0xfc3dd3accd000f33 0xbf0f74eb334003cc

def z535 : W := mkw 0x8000000550209856 0xa000000154082615 0x0000000ff0000000 0x00000003fc000000

def z536 : W := mkw 0x041cd1acc52c5b30 0xc107346b314b16cc 0xfc3fd3fccffc7fff 0xff0ff4ff33ff1fff

def z537 : W := mkw 0x026600000f8006a8 0x0099800003e001aa 0xf7fe00000fc00ffc 0xfdff800003f003ff

def z538 : W := mkw 0x022e013005800228 0x008b804c0160008a 0x703e007003c008fe 0xdc0f801c00f0023f

def z539 : W := mkw 0x018162ce00240900 0x006058b380090240 0xefc1e3cf0c3c0f03 0x7bf078f3c30f03c0

def z540 : W := mkw 0x0dd1f2cfca3eddd3 0xc3747cb3f28fb774 0xefc1f3cfce3fffc3 0x7bf07cf3f38ffff0

def z541 : W := mkw 0x800004011041a046 0x2000010044106811 0x0000000002c380cc 0x0000000000b0e033

def z542 : W := mkw 0x008843faa0000000 0x002210fea8000000 0x0800038000000000 0x020000e000000000

def z543 : W := mkw 0x026200000a800000 0x0098800002a00000 0x03c2000002c00000 0x40f0800000b00000

def z544 : W := mkw 0x03b3ba5220000000 0x00ecee9488000000 0xd3fffc5330000001 0xf4ffff14cc000000

def z545 : W := mkw 0x063ed9bce52c5b30 0xc18fb66f394b16cc 0xfc3fdfbcfd3c7f33 0xbf0ff7ef3f4f1fcc

def z546 : W := mkw 0x036720000f920000 0x00d9c80003e48000 0xf7ffe0000fff8001 0xfdfff80003ffe000

def z547 : W := mkw 0x0aee03750fb68feb 0x02bb80dd43eda3fa 0xfffe03f00fff8ffe 0xffff80fc03ffe3ff

def z548 : W := mkw 0x0101200000120000 0x0040480000048000 0x0001e000003f8001 0x00007800000fe000

def z549 : W := mkw 0x13bbfffaa05b6000 0x04eefffea816d800 0xdbfffffff03ff003 0xf6fffffffc0ffc00

def z550 : W := mkw 0x8000040050413014 0xa000010014104c05 0x0000000001c0703c 0x0000000000701c0f

def z551 : W := mkw 0x0000040000412000 0x0000010000104800 0x60023c7ff3e3f003 0xd8008f1ffcf8fc00

def z552 : W := mkw 0x051df9aee52c5b30 0xc1477e6bb94b16cc 0xfc3dffaffd3c7f33 0xbf0f7febff4f1fcc

def z553 : W := mkw 0x02ba9b70a0000000 0x00aea6dc28000000 0xdbfe1ff0f0000002 0xf6ff87fc3c000000

def z554 : W := mkw 0x823a9d30f0413014 0xa08ea74c3c104c05 0x103e1c30f1c0703c 0x840f870c3c701c0f

def z555 : W := mkw 0x13bffffaa5c96000 0x04effffea9725800 0xdbfffffff1c07003 0xf6fffffffc701c00

def z556 : W := mkw 0x040c41acc5241b30 0xc103106b314906cc 0xfc3c03accd000f32 0xbf0f00eb334003cc

def z557 : W := mkw 0x1337bc0005c96000 0x04cdef0001725800 0xd3fffc0001c07001 0xf4ffff0000701c00

def z558 : W := mkw 0x022a013000000000 0x008a804c00000000 0x103e003000000000 0x840f800c00000000

def z559 : W := mkw 0x904404055ffbf856 0xa411010157fefe15 0x64023c7ffffff8ff 0xd9008f1ffffffe3f

def z560 : W := mkw 0x041c9120c5085230 0xc10724483142148c 0xf43dd020cd3c7031 0xbd0f7408334f1c0c

def z561 : W := mkw 0x126604000fdb6000 0x0499810003f6d800 0xf7fe00000ffff000 0xfdff800003fffc00

def z562 : W := mkw 0x00109800a0000000 0x0004260028000000 0x00001c00f0000000 0x000007003c000000

def z563 : W := mkw 0x03e32a522a800488 0x00f8ca948aa00122 0x03c22c5332c000cc 0x40f08b14ccb00033

def z564 : W := mkw 0x04109000c0085010 0xc104240030021404 0x00001000c0007000 0x0000040030001c00

def z565 : W := mkw 0x023ad9b8a0000000 0x008eb66e28000000 0xd83fdfbcf0000003 0xb60ff7ef3c000000

def z566 : W := mkw 0x03fbfbfaaa800488 0x00fefefeaaa00122 0xdbfffffff2c000cf 0xf6fffffffcb00033

def z567 : W := mkw 0x104404000fdb66a8 0x0411010003f6d9aa 0x240000000ffffffc 0x0900000003ffffff

def z568 : W := mkw 0x19d1fecf0a7fedc3 0x06747fb3c29ffb70 0xefc1ffcf0e3fffc3 0x7bf07ff3c38ffff0

def z569 : W := mkw 0x0bef63ff0fb68feb 0x02fbd8ffc3eda3fa 0xfffde3cf0e3f8fc3 0x7fff78f3c38fe3f0

def z570 : W := mkw 0x03a32a5220000000 0x00e8ca9488000000 0x03c0000000000000 0x00f0000000000000

def z571 : W := mkw 0x0098d3faa0000000 0x002634fea8000000 0xd83dd3fff0000003 0xb60f74fffc000000

def z572 : W := mkw 0x8410d48dd06df956 0xe1043523741b7e55 0x0001fc0ff03ff001 0x00007f03fc0ffc00

def z573 : W := mkw 0x9bf7fecf5ffffdd7 0xa6fdffb3d7ffff75 0xffffffffffffffff 0xffffffffffffffff

def z574 : W := mkw 0x0000000000000000 0x0000000000000000 0x60023c7ff3c008ff 0xd8008f1ffcf0023f

def z575 : W := mkw 0x00c042cc0a240d80 0x003010b302890360 0xefc1c3cc0e3c0fc3 0x7bf070f3038f03f0

def z576 : W := mkw 0x1377bc000fdb6000 0x04ddef0003f6d800 0x97ffdc000ddc7000 0xa5fff70003771c00

def z577 : W := mkw 0x0000408d00248942 0x0000102340092250 0xec01e3cf0e3f8fc3 0x7b0078f3c38fe3f0

def z578 : W := mkw 0x1377fc8c0fff6900 0x04ddff2303ffda40 0xffffff8c0fffff03 0xffffffe303ffffc0

def z579 : W := mkw 0x0000000000000000 0x0000000000000000 0xec0003800c000f02 0x3b0000e0030003c0

def z580 : W := mkw 0x01c162ca0a120000 0x007058b282848000 0xefc1e3cf0e3f8003 0x7bf078f3c38fe000

def z581 : W := mkw 0x03bffbfaa5084000 0x00effefea9421000 0xfffffffffd3c7003 0xffffffffff4f1c00

def z582 : W := mkw 0x00c803700a0006a8 0x003200dc028001aa 0xefc003f00e000ffe 0x7bf000fc038003ff

def z583 : W := mkw 0x0bef63fa0f9607a9 0x02fbd8fe83e581ea 0xffffc3f00fdc0ffe 0xfffff0fc03f703ff

def z584 : W := mkw 0x06bed3fcc52c5b30 0xc1afb4ff314b16cc 0xffffd3fccd3c7f33 0xfffff4ff334f1fcc

def z585 : W := mkw 0x084000050a368dc3 0x02100001428da370 0x6400204f0e3f8fc3 0x59000813c38fe3f0

def z586 : W := mkw 0x02ee03700f8006a8 0x00bb80dc03e001aa 0xfffc03a00d000f32 0xbfff00e8034003cc

def z587 : W := mkw 0x82ee03755fa09efe 0xa0bb80dd57e827bf 0xfffe03ffffc00ffe 0xffff80fffff003ff

def z588 : W := mkw 0x1111b800001a4000 0x04446e0000069000 0x0001c000001c0000 0x0000700000070000

def z589 : W := mkw 0x059df3eec52c5b30 0xc1677cfbb14b16cc 0xfffdf3efcd3c7f33 0xffff7cfbf34f1fcc

def z590 : W := mkw 0x0101200000000000 0x0040480000000000 0xc3c1e00000000001 0x70f0780000000000

def z591 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000007ff0000002 0x0000001ffc000000

def z592 : W := mkw 0x0014900445285810 0x80052401114a1604 0xf43dd02ccd3c7833 0xbd0f740b334f1e0c

def z593 : W := mkw 0x02fed3f88f8006a8 0x00bfb4fe23e001aa 0xffffd3fccfc00fff 0xfffff4ff33f003ff

def z594 : W := mkw 0x104004000ad32000 0x0410010002b4c800 0x0000000002c38000 0x0000000000b0e000

def z595 : W := mkw 0x088042ca00040581 0x022010b280010160 0x0800038000000700 0x020000e0000001c0

def z596 : W := mkw 0x049cd3fcc52c5fb8 0xc12734ff314b17ee 0xfc3dd3fccd3c7fff 0xbf0f74ff334f1fff

def z597 : W := mkw 0x93fffffffffbf856 0xa4fffffffffefe15 0xfffffffffffff8ff 0xfffffffffffffe3f

def z598 : W := mkw 0x0333bc0000412000 0x00ccef0000104800 0xf3fffc0003e3f001 0xfcffff0000f8fc00

def z599 : W := mkw 0x888046cf5065bdd7 0xa22011b3d4196f75 0x68023ffff3e3ffff 0xda008ffffcf8ffff

def z600 : W := mkw 0x088843ff00248feb 0x022210ffc00923fa 0x080003ff00000ffe 0x020000ffc00003ff

def z601 : W := mkw 0x1377bc050ffbe842 0x04ddef0143fefa10 0xf7fffc4f0ffff8c3 0xfdffff13c3fffe30

def z602 : W := mkw 0x1155bc000fdb6000 0x04556f0003f6d800 0x2401fc000ffff001 0x09007f0003fffc00

def z603 : W := mkw 0x0377b8000f800000 0x00ddee0003e00000 0xf7fffc000fc00001 0xfdffff0003f00000

def z604 : W := mkw 0x026600000f800000 0x0099800003e00000 0x97fc00000c000000 0x25ff000003000000

def z605 : W := mkw 0x13e32e522ad32000 0x04f8cb948ab4c800 0x03c22c5332c38000 0x40f08b14ccb0e000

def z606 : W := mkw 0x8000448d5065b956 0xa000112354196e55 0xec03ffffffffffff 0xfb00ffffffffffff

def z607 : W := mkw 0x02ae0370058006a8 0x00ab80dc016001aa 0x183e03f001c00ffe 0x860f80fc007003ff

def z608 : W := mkw 0x9111bc05507bf856 0xa4446f01541efe15 0x6003fc7ff3fff8ff 0xd800ff1ffcfffe3f

def z609 : W := mkw 0x1777bc044fff7b30 0xc5ddef0113ffdecc 0xf7fffc000fffff31 0xfdffff0003ffffcc

def z610 : W := mkw 0x0d11f08fc03ed953 0xc3447c23f00fb654 0x0001f00fc03ff001 0x00007c03f00ffc00

def z611 : W := mkw 0x93ffbf755ffbfefe 0xa4ffefdd57feffbf 0xffffffffffffffff 0xffffffffffffffff

def z612 : W := mkw 0x00880370000006a8 0x002200dc000001aa 0x0800038000000700 0x020000e0000001c0

def z613 : W := mkw 0x0511f88ee02c5910 0xc1447e23b80b1644 0x0001fc0ff03c7001 0x00007f03fc0f1c00

def z614 : W := mkw 0x0000000000000000 0x0000000000000000 0x6000002001000832 0x980000080040020c

def z615 : W := mkw 0x0000000440201810 0x8000000110080604 0x60023c7ff1207833 0xd8008f1ffc481e0c

def z616 : W := mkw 0x03fffbfaaf800000 0x00fffefeabe00000 0xffffffffffc00003 0xfffffffffff00000

def z617 : W := mkw 0x8bfbfffffa77bdd7 0xa2fefffffe9def75 0xffffffffffffffff 0xffffffffffffffff

def z618 : W := mkw 0x08c042cf0a368dc3 0x023010b3c28da370 0x2c0003cf0e3f8fc2 0x0b0000f3c38fe3f0

def z619 : W := mkw 0x1511fc8cc07f7910 0xc5447f23301fde44 0x0001fc0cc03ff001 0x00007f03300ffc00

def z620 : W := mkw 0x13fbfffaaad32000 0x04fefffeaab4c800 0xdbfffffff2c38003 0xf6fffffffcb0e000

def z621 : W := mkw 0x83bbfffff061b856 0xa0eefffffc186e15 0xdbfffffff023f003 0xf6fffffffc08fc00

def z622 : W := mkw 0x03bbfbfaa0000000 0x00eefefea8000000 0xdbfdd3acc0000003 0xb6ff74eb30000000

def z623 : W := mkw 0x041cd5acc56d7b30 0xc107356b315b5ecc 0xfc3fffaccfffff33 0xff0fffeb33ffffcc

def z624 : W := mkw 0x09c166cf0a77adc3 0x027059b3c29deb70 0xefc3ffcf0fffffc3 0xfbf0fff3c3fffff0

def z625 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z626 : W := mkw 0x1bffffffafffedc3 0x06ffffffebfffb70 0xffffffffffffffc3 0xfffffffffffffff0

def z627 : W := mkw 0x0000000500208842 0x0000000140082210 0x0000200f00238001 0x00000803c008e000

def z628 : W := mkw 0x09c122430a1284c3 0x02704890c284a130 0xe7c1e0430e3f80c1 0x79f07810c38fe030

def z629 : W := mkw 0x02ea03700a8006a8 0x00ba80dc02a001aa 0x0bc203f002c00ffe 0x42f080fc00b003ff

def z630 : W := mkw 0x00c002400a000480 0x0030009002800120 0xefc203f00fc00ffe 0xfbf080fc03f003ff

def z631 : W := mkw 0x0008012000000000 0x0002004800000000 0xd83c03a000000002 0xb60f00e800000000

def z632 : W := mkw 0x0941608f0a368dc3 0x02505823c28da370 0x2401e00f0e3f8fc1 0x09007803c38fe3f0

def z633 : W := mkw 0x89c166cf5a77bdd7 0xa27059b3d69def75 0xefc1ffcffe3fffc3 0x7bf07ff3ff8ffff0

def z634 : W := mkw 0x818166cf5061b856 0xa06059b3d4186e15 0xebc3fffff3e3f8ff 0xfaf0fffffcf8fe3f

def z635 : W := mkw 0x0000000400200800 0x0000000100080200 0x6000000c00200803 0x1800000300080200

def z636 : W := mkw 0x8000000110008046 0x2000000044002011 0x00000053300000cc 0x00000014cc000033

def z637 : W := mkw 0x137fbd300fdb6228 0x04dfef4c03f6d88a 0xf7fffc300ffff03d 0xfdffff0c03fffc0f

def z638 : W := mkw 0x02e602500f8006a8 0x00b9809403e001aa 0x27c200500fc00ffc 0x49f0801403f003ff

def z639 : W := mkw 0x022e013005800228 0x008b804c0160008a 0x103c000000000000 0x040f000000000000

def z640 : W := mkw 0x041c9124c52c5b30 0xc1072449314b16cc 0x343c1020cd3c7f30 0x8d0f0408334f1fcc

def z641 : W := mkw 0x1bf7faca0f9e4581 0x06fdfeb283e79160 0x9ffdc3800c1c0700 0x27ff70e0030701c0

def z642 : W := mkw 0x93632c011ad3a046 0x24d8cb0046b4e811 0x03c22c5332c380cc 0x40f08b14ccb0e033

def z643 : W := mkw 0x0119f9aaa0000000 0x00467e6aa8000000 0xd83dffaff0000003 0xb60f7febfc000000

def z644 : W := mkw 0x041cd1a8850c4320 0x4107346a214310c8 0xfc3dc3a00d1c0f32 0xbf0f70e8034703cc

def z645 : W := mkw 0x088843ffa0248dc3 0x022210ffe8092370 0x080003fff0000fc2 0x020000fffc0003f0

def z646 : W := mkw 0x00cc03600f0006a0 0x003300d803c001a8 0xfffc03e00f000ff2 0xffff00f803c003fc

def z647 : W := mkw 0x11012c0000532000 0x04404b000014c800 0x00002c0000038000 0x00000b000000e000

def z648 : W := mkw 0x033bf9baa0000000 0x00cefe6ea8000000 0x103ffc3ff0000001 0x840fff0ffc000000

def z649 : W := mkw 0x177fbd20cfdb7230 0xc5dfef4833f6dc8c 0xf7fffc20cffff031 0xfdffff0833fffc0c

def z650 : W := mkw 0x0414d08cc52c5910 0xc1053423314b1644 0xf43dd00ccd3c7001 0xbd0f7403334f1c00

def z651 : W := mkw 0x07bffbfaa50c4320 0x41effefea94310c8 0xdffffffffc1c0703 0xf7ffffffff0701c0

def z652 : W := mkw 0x00080130a0000000 0x0002004c28000000 0x00000030f0000000 0x0000000c3c000000

def z653 : W := mkw 0x84040405556dfb76 0xe1010101555b7edd 0x240000000ffffffc 0x0900000003ffffff

def z654 : W := mkw 0x03bbfbfaa0000000 0x00eefefea8000000 0x9bfdc3fff0000002 0x26ff70fffc000000

def z655 : W := mkw 0x800004055061b856 0xa000010154186e15 0x20003c0ff3e3f8fd 0x08000f03fcf8fe3f

def z656 : W := mkw 0x02ee03700f8006a8 0x00bb80dc03e001aa 0x9ffe03d00ec007cc 0x67ff80f403b001f3

def z657 : W := mkw 0x0014900005084000 0x0005240001421000 0x103c100001007000 0x840f040000401c00

def z658 : W := mkw 0x0bfbfbfbaa1284c3 0x02fefefeea84a130 0xdbfffffff20380c3 0xf6fffffffc80e030

def z659 : W := mkw 0x0000000000000000 0x0000000000000000 0x6000100001207001 0x9800040000481c00

def z660 : W := mkw 0x0c9cd3efc52cdff3 0xc32734fbf14b37fc 0xfc3dd3efcd3c7ff3 0xbf0f74fbf34f1ffc

def z661 : W := mkw 0x026600000f800000 0x0099800003e00000 0xf7fe00700fc008fe 0xfdff801c03f0023f

def z662 : W := mkw 0x0222000000000000 0x0088800000000000 0xd3fe000000000000 0xf4ff800000000000

def z663 : W := mkw 0x800004055061b856 0xa000010154186e15 0x20021c30f3e3f8fc 0x8800870c3cf8fe3f

def z664 : W := mkw 0x83bbfffbb041a046 0x20eefffeec106811 0xdbfffffff2c380cf 0xf6fffffffcb0e033

def z665 : W := mkw 0x0bbbfbffa0248dc3 0x02eefeffe8092370 0xdbfffffff0000fc3 0xf6fffffffc0003f0

def z666 : W := mkw 0x0404408c452c5b30 0xc1011023114b16cc 0xec01c38c0d3c7f33 0x3b0070e3034f1fcc

def z667 : W := mkw 0x0800000500248dc3 0x0200000140092370 0x0000000000000fc0 0x00000000000003f0

def z668 : W := mkw 0x841c9525d569fa76 0xe1072549755a7e9d 0x703e3c7ff3e3f8ff 0xdc0f8f1ffcf8fe3f

def z669 : W := mkw 0x1377b8000f9a4000 0x04ddee0003e69000 0xf7ffc0000fdc0000 0xfdfff00003f70000

def z670 : W := mkw 0x09c963ffaa368dc3 0x027258ffea8da370 0xefc1e3fffe3f8fc3 0x7bf078ffff8fe3f0

def z671 : W := mkw 0x800004055061b856 0xa000010154186e15 0x40023c7ff023f003 0xd0008f1ffc08fc00

def z672 : W := mkw 0x800004055061b856 0xa000010154186e15 0x6000102cc3e3f8ff 0x9800040b30f8fe3f

def z673 : W := mkw 0x8000040010412004 0x2000010004104801 0x00020c1030c0000c 0x000083040c300003

def z674 : W := mkw 0x1b77fc8f0fffe943 0x06ddff23c3fffa50 0xf7fffc0f0ffff001 0xfdffff03c3fffc00

def z675 : W := mkw 0x105494000fdb6000 0x0415250003f6d800 0xf43dd0000ffff001 0xbd0f740003fffc00

def z676 : W := mkw 0x0373b8000a120000 0x00dcee0002848000 0xf7fffc000e3f8001 0xfdffff00038fe000

def z677 : W := mkw 0x1377fc8aafdb6000 0x04ddff22abf6d800 0xf7fffc0ffffff001 0xfdffff03fffffc00

def z678 : W := mkw 0x800004055061b856 0xa000010154186e15 0x00003c7ff023f8ff 0x00000f1ffc08fe3f

def z679 : W := mkw 0x0400000440241b30 0xc1000001100906cc 0x0000000000000f30 0x00000000000003cc

def z680 : W := mkw 0x1377bc000fdb6000 0x04ddef0003f6d800 0x13fe3c0003c3f000 0xc4ff8f0000f0fc00

def z681 : W := mkw 0x0018d1a880000000 0x0006346a20000000 0x983dc38000000000 0x260f70e000000000

def z682 : W := mkw 0x800004011041a046 0x2000010044106811 0x40023c7ff2c380cf 0xd0008f1ffcb0e033

def z683 : W := mkw 0x0bfbfbfaaa160581 0x02fefefeaa858160 0xdffffffffc1c0703 0xf7ffffffff0701c0

def z684 : W := mkw 0x82ee07755fe1befe 0xa0bb81dd57f86fbf 0xfffe03f00fe3fffe 0xffff80fc03f8ffff

def z685 : W := mkw 0x0000000000000000 0x0000000000000000 0x0002005002c000cc 0x4000801400b00033

def z686 : W := mkw 0x0418d1acc0241b30 0xc106346b300906cc 0xd83dd3acc0000f33 0xb60f74eb300003cc

def z687 : W := mkw 0x0000000500208842 0x0000000140082210 0x0000004f000008c2 0x00000013c0000230

def z688 : W := mkw 0x800004055061b856 0xa000010154186e15 0x6000204f03e3f8ff 0x58000813c0f8fe3f

def z689 : W := mkw 0x104400000f9a4000 0x0411000003e69000 0x040000000c1c0000 0x0100000003070000

def z690 : W := mkw 0x0000000500208842 0x0000000140082210 0x20000000022388c0 0x080000000088e230

def z691 : W := mkw 0x92369c0555e9f856 0xa48da701557a7e15 0x703e3c7ff3e3f8ff 0xdc0f8f1ffcf8fe3f

def z692 : W := mkw 0x800004055061b856 0xa000010154186e15 0x6002007003e3f8fe 0xd800801c00f8fe3f

def z693 : W := mkw 0x0000000000000000 0x0000000000000000 0x00003c0ff0000001 0x00000f03fc000000

def z694 : W := mkw 0x123e9d30a5c96000 0x048fa74c29725800 0x103e1c30f1c07000 0x840f870c3c701c00

def z695 : W := mkw 0x02ee03700f8006a8 0x00bb80dc03e001aa 0x9ffc03f00c000ffe 0x27ff00fc030003ff

def z696 : W := mkw 0x13f7be400fdb6480 0x04fdef9003f6d920 0xffffffc00fffffc3 0xfffffff003fffff0

def z697 : W := mkw 0x13f7be522fdb6000 0x04fdef948bf6d800 0xf7fffc533ffff001 0xfdffff14cffffc00

def z698 : W := mkw 0x800004055061b856 0xa000010154186e15 0x000000000023f000 0x000000000008fc00

def z699 : W := mkw 0x0000408800000000 0x0000102200000000 0xc801c38c00000003 0x320070e300000000

def z700 : W := mkw 0x1004040005c96000 0x0401010001725800 0x0000000001c07000 0x0000000000701c00

def z701 : W := mkw 0x977ffdaddffffb76 0xe5dfff6b77fffedd 0xffffffffffffffff 0xffffffffffffffff

def z702 : W := mkw 0x822e053055c1323c 0xa08b814c15704c8f 0x103e1c30f1c0703c 0x840f870c3c701c0f

def z703 : W := mkw 0x018162ca00000000 0x006058b280000000 0x8bc1c38000000000 0x22f070e000000000

def z704 : W := mkw 0x1377b8000f9a4000 0x04ddee0003e69000 0xd7fffc000c1c0001 0xf5ffff0003070000

def z705 : W := mkw 0x800004055061b856 0xa000010154186e15 0x00023c3ff1e3f03d 0x80008f0ffc78fc0f

def z706 : W := mkw 0x0000040000412000 0x0000010000104800 0x00022c0002c38000 0x40008b0000b0e000

def z707 : W := mkw 0x03bbfbfaa0000220 0x00eefefea8000088 0xdbfffffff0000f33 0xf6fffffffc0003cc

def z708 : W := mkw 0x1377bc100fdb6008 0x04ddef0403f6d802 0xf7fffc100ffff00d 0xfdffff0403fffc03

def z709 : W := mkw 0x13e32e400ad32480 0x04f8cb9002b4c920 0x03c22c4002c380c0 0x40f08b1000b0e030

def z710 : W := mkw 0x09c162cf0a368dc3 0x027058b3c28da370 0xefc1e38f0e3f8701 0x7bf078e3c38fe1c0

def z711 : W := mkw 0x984404055ffffdd7 0xa611010157ffff75 0x240000000ffffffc 0x0900000003ffffff

def z712 : W := mkw 0x03ab2b7220000000 0x00eacadc88000000 0xdbfe3ffff0000003 0xf6ff8ffffc000000

def z713 : W := mkw 0x83bbfffff061b856 0xa0eefffffc186e15 0xbbfdc38003e3f8fc 0x2eff70e000f8fe3f

def z714 : W := mkw 0x041cd1a8c50c5330 0xc107346a314314cc 0xfc3dd3a0cd3c7731 0xbf0f74e8334f1dcc

def z715 : W := mkw 0x041cd1adc52cdb72 0xc107346b714b36dc 0xfc3fffffff3ffff3 0xff0fffffffcffffc

def z716 : W := mkw 0x041cd1acc52c5b30 0xc107346b314b16cc 0xfc3df3accf3fff33 0xff0f7ceb33cfffcc

def z717 : W := mkw 0x0014d088050c4100 0x0005342201431040 0xfc3dd3800d3c7701 0xbf0f74e0034f1dc0

def z718 : W := mkw 0x03bbfbfaa0000000 0x00eefefea8000000 0xfbfffffff3c00003 0xfefffffffcf00000

def z719 : W := mkw 0x041cd1acc52c5b30 0xc107346b314b16cc 0xfc3dd3fccd3c7fff 0xbf0f74ff334f1fff

def z720 : W := mkw 0x00cc03600f0006a0 0x003300d803c001a8 0xfffe03f00fc00ffe 0xffff80fc03f003ff

def z721 : W := mkw 0x03bbfbfaa0000000 0x00eefefea8000000 0xfbfffffff1207003 0xfefffffffc481c00

def z722 : W := mkw 0x041cd1acc5ac5b38 0xc107346b316b16ce 0xfc3dd3accdfc7f3f 0xbf0f74eb337f1fcf

def z723 : W := mkw 0x1377bc000fdb6000 0x04ddef0003f6d800 0xffffff800fffff03 0xffffffe003ffffc0

def z724 : W := mkw 0x0333b80000000000 0x00ccee0000000000 0xd3fffc0ff0000001 0xf4ffff03fc000000

def z725 : W := mkw 0x018162cf00248942 0x006058b3c0092250 0xefc1e3cf0e3f8fc3 0x7bf078f3c38fe3f0

def z726 : W := mkw 0x02ee03722f8006a8 0x00bb80dc8be001aa 0xfffe03f33fc00ffe 0xffff80fccff003ff

def z727 : W := mkw 0x0333f88aa0000000 0x00ccfe22a8000000 0x93fdfc0ff0000001 0x24ff7f03fc000000

def z728 : W := mkw 0x033bb930a0000000 0x00ceee4c28000000 0xd3fffc7ff0000003 0xf4ffff1ffc000000

def z729 : W := mkw 0x041cd1acc52c5b30 0xc107346b314b16cc 0xfc3dd3800d3c7f31 0xbf0f74e0034f1fcc

def z730 : W := mkw 0x02ee03700f8846a8 0x00bb80dc03e211aa 0xfffe03f00ffc7ffe 0xffff80fc03ff1fff

def z731 : W := mkw 0x09c162cf0a368dc3 0x027058b3c28da370 0xefc1e3800e3f8fc1 0x7bf078e0038fe3f0

def z732 : W := mkw 0x041cd1a8850c4320 0x4107346a214310c8 0xbc3dc3800d3c7700 0x2f0f70e0034f1dc0

def z733 : W := mkw 0x9377b8055fbad856 0xa4ddee0157eeb615 0x97fdc07ffc1c08fe 0x25ff701fff07023f

def z734 : W := mkw 0x0155f88aaf8006a8 0x00557e22abe001aa 0x2401fc0fffc00ffd 0x09007f03fff003ff

def z735 : W := mkw 0x041cd1acc52c5b30 0xc107346b314b16cc 0xfc3dd38ccc3c7f03 0x3f0f74e3330f1fc0

def z736 : W := mkw 0x89c166ca5a573595 0xa27059b29695cd65 0x8fc3dfb0fddc773c 0xa3f0f7ec3f771dcf

def z737 : W := mkw 0x09c162cf0a368dc3 0x027058b3c28da370 0xafc1e3c30e3f8fc0 0x6bf078f0c38fe3f0

def z738 : W := mkw 0x841cd1add52cdb76 0xe107346b754b36dd 0xfc3ffffffd3c7fff 0xff0fffffff4f1fff

def z739 : W := mkw 0x176b6daccaf73b30 0xc5dadb6b32bdcecc 0x0bc22facc2c38f32 0x42f08beb30b0e3cc

def z740 : W := mkw 0x123e9d2005c96220 0x048fa74801725888 0x103e1c2001c07030 0x840f870800701c0c

def z741 : W := mkw 0x09c162cf0a368dc3 0x027058b3c28da370 0xefc3e3cf0fff8fc3 0xfbf0f8f3c3ffe3f0

def z742 : W := mkw 0x8c4404055f7ffff7 0xe311010157dffffd 0x240000000ffffffc 0x0900000003ffffff

def z743 : W := mkw 0x09c162cf0a368dc3 0x027058b3c28da370 0xefc1e3ef0f3f8ff3 0xfbf078fbc3cfe3fc

def z744 : W := mkw 0x041cd1bcc52c5b38 0xc107346f314b16ce 0xfc3dd3bccd3c7f3f 0xbf0f74ef334f1fcf

def z745 : W := mkw 0x804404055fe1b856 0xa011010157f86e15 0x240000000fe3f8fc 0x0900000003f8fe3f

def z746 : W := mkw 0x13e32e500ad32488 0x04f8cb9402b4c922 0x03c22c0002c38000 0x40f08b0000b0e000

def z747 : W := mkw 0x041cd1acc52c5b30 0xc107346b314b16cc 0xfc3ffffffffc7fff 0xff0fffffffff1fff

def z748 : W := mkw 0x841cd1add52cdb76 0xe107346b754b36dd 0xfc3dd3affd3c7f33 0xbf0f74ebff4f1fcc

def z749 : W := mkw 0x09c162ca0a160581 0x027058b282858160 0xefc1e3c00e3f8fc3 0x7bf078f0038fe3f0

def z750 : W := mkw 0x02ee03700f8006a8 0x00bb80dc03e001aa 0xfffe13fccfc00fff 0xffff84ff33f003ff

def z751 : W := mkw 0x1377bc000fdb66a8 0x04ddef0003f6d9aa 0xf7fffc000ffff701 0xfdffff0003fffdc0

def z752 : W := mkw 0x09c162cf0a368dc3 0x027058b3c28da370 0x8fc1e3cf0e3f87c1 0x63f078f3c38fe1f0

def z753 : W := mkw 0x041cd1a8850c4320 0x4107346a214310c8 0x9c3dd3800c3c7701 0x270f74e0030f1dc0

def z754 : W := mkw 0x02aa0370000006a8 0x00aa80dc000001aa 0xfbfe03f003c00ffe 0xfeff80fc00f003ff

def z755 : W := mkw 0x8c8843efd0249ff7 0xe32210fbf40927fd 0x080003fff0000ffe 0x020000fffc0003ff

def z756 : W := mkw 0x163e9d30c5c97238 0xc58fa74c31725c8e 0x103e1c30c1c0703c 0x840f870c30701c0f

def z757 : W := mkw 0x1377bc000fdb6000 0x04ddef0003f6d800 0xf7fffc2ccffff003 0xfdffff0b33fffc00

def z758 : W := mkw 0x03bbfbfaa0000000 0x00eefefea8000000 0x9bffeffff0000002 0x66fffbfffc000000

def z759 : W := mkw 0x1ab6decf05ededc3 0x06adb7b3c17b7b70 0x183e1fcf01c07fc2 0x860f87f3c0701ff0

def z760 : W := mkw 0x03ab6bfaa0000000 0x00eadafea8000000 0xdbfe2ffff0000002 0xf6ff8bfffc000000

def z761 : W := mkw 0x041cd1adc52cdb72 0xc107346b714b36dc 0xfc3df3afcd3fff33 0xbf0f7cebf34fffcc

def z762 : W := mkw 0x041cd1adc52cdb72 0xc107346b714b36dc 0xfc3dd3accf3ffff3 0xbf0f74eb33cffffc

def z763 : W := mkw 0x09c162cf0a368dc3 0x027058b3c28da370 0xefc1e3cf0fff8fff 0x7bf078f3c3ffe3ff

def z764 : W := mkw 0x06f2d2dccaac5d98 0xc1bcb4b732ab1766 0x03c3d05cc2fc70cd 0x40f0f41730bf1c33

def z765 : W := mkw 0x82ee07755fe1befe 0xa0bb81dd57f86fbf 0x9ffc3f8ffc23f701 0x27ff0fe3ff08fdc0

def z766 : W := mkw 0x09c162cf0a368dc3 0x027058b3c28da370 0xefc1f3efce3f8fc3 0xfbf07cfbf38fe3f0

def z767 : W := mkw 0x041cd1acc52c5b30 0xc107346b314b16cc 0xfc3dc38c0d3c7f33 0x3f0f70e3034f1fcc

def z768 : W := mkw 0x01c162cc0a360d80 0x007058b3028d8360 0xefc1e3cc0e3f8fc3 0x7bf078f3038fe3f0

def z769 : W := mkw 0x0199fbeaa0000000 0x00667efaa8000000 0xdbfdffeff0000003 0xf6ff7ffbfc000000

def z770 : W := mkw 0x0941608f0a368943 0x02505823c28da250 0xefc1e38f0e3f8f03 0x7bf078e3c38fe3c0

def z771 : W := mkw 0x041cd1acc52c5b30 0xc107346b314b16cc 0xfc3dc3a00d3c7f32 0xbf0f70e8034f1fcc

def z772 : W := mkw 0x0155b4000f5b6000 0x00556d0003d6d800 0xf7fffc000ffff001 0xfdffff0003fffc00

def z773 : W := mkw 0x07bbfbfaa0040320 0x41eefefea80100c8 0xdbfffffff0000703 0xf6fffffffc0001c0

def z774 : W := mkw 0x001c912005084220 0x0007244801421088 0xfc3dd3800d3c7701 0xbf0f74e0034f1dc0

def z775 : W := mkw 0x02ee0b702f8006a8 0x00bb82dc0be001aa 0xfffe0ff03fc00ffe 0xffff83fc0ff003ff

def z776 : W := mkw 0x0dddb363cf1ad6f3 0xc3776cd8f3c6b5bc 0x13fc3063c303f0f0 0xc4ff0c18f0c0fc3c

def z777 : W := mkw 0x02ee03700f8006a8 0x00bb80dc03e001aa 0x9ffe03f00ec00ffe 0x67ff80fc03b003ff

def z778 : W := mkw 0x02ee03700f8006a8 0x00bb80dc03e001aa 0xfffe23f00fe38fff 0xffff88fc03f8e3ff

def z779 : W := mkw 0x041cd1acc52c5b30 0xc107346b314b16cc 0xbc3dd38ccd3c7f31 0x2f0f74e3334f1fcc

def z780 : W := mkw 0x09c162cfaa368dc3 0x027058b3ea8da370 0xefc1e3cffe3f8fc3 0x7bf078f3ff8fe3f0

def z781 : W := mkw 0x03bbfbfaa0000000 0x00eefefea8000000 0xdbfffffff1c0003f 0xf6fffffffc70000f

def z782 : W := mkw 0x02ee03700f8006a8 0x00bb80dc03e001aa 0xfffc03c00fc00ffe 0x7fff00f003f003ff

def z783 : W := mkw 0x1377bc000fdb6000 0x04ddef0003f6d800 0xf7fdfc000d3ff001 0xbdff7f00034ffc00

def z784 : W := mkw 0x1199bf70005b66a8 0x04666fdc0016d9aa 0x0801fff0003fffff 0x02007ffc000fffff

def z785 : W := mkw 0x0941608d0a368dc3 0x02505823428da370 0xefc1e38c0e3f8fc3 0x7bf078e3038fe3f0

def z786 : W := mkw 0x8be32e533a53a4c7 0x22f8cb94ce94e931 0x03c22c5332c380cc 0x40f08b14ccb0e033

def z787 : W := mkw 0x963e9d20d5c97234 0xe58fa74835725c8d 0x103e1c30f1c0703c 0x840f870c3c701c0f

def z788 : W := mkw 0x841cd5a9954de366 0x6107356a655378d9 0x9c3fefd33edf87cc 0x670ffbf4cfb7e1f3

def z789 : W := mkw 0x0141608d0a368942 0x00505823428da250 0xefc1e3cf0e3f8fc3 0x7bf078f3c38fe3f0

def z790 : W := mkw 0x01c162ca0a120480 0x007058b282848120 0xefc1e3cf0e3f8fc3 0x7bf078f3c38fe3f0

def z791 : W := mkw 0x1377bc000fdb6228 0x04ddef0003f6d88a 0xf7fffc000ffff03d 0xfdffff0003fffc0f

def z792 : W := mkw 0x041cd1acc52c5b30 0xc107346b314b16cc 0xbc3dd3a0cd3c7f30 0xaf0f74e8334f1fcc

def z793 : W := mkw 0x9377bc001fdb6004 0x24ddef0007f6d801 0xf7fffc103ffff00d 0xfdffff040ffffc03

def z794 : W := mkw 0x041cd1acc52c5b30 0xc107346b314b16cc 0xfc3dd3accffc7fff 0xbf0f74eb33ff1fff

def z795 : W := mkw 0x841cd1add52cdb76 0xe107346b754b36dd 0xfc3dd3accd3c7fff 0xbf0f74eb334f1fff

def z796 : W := mkw 0x041cd1a8c50c5330 0xc107346a314314cc 0xfc3dd3a0cd1c7f32 0xbf0f74e833471fcc

def z797 : W := mkw 0x1377bc000fdb6000 0x04ddef0003f6d800 0xd7fffc000c3ff001 0xf5ffff00030ffc00

def z798 : W := mkw 0x8511fc8ff06df956 0xe1447f23fc1b7e55 0x0001fc0ff03ff001 0x00007f03fc0ffc00

def z799 : W := mkw 0x02ee03700f8006a8 0x00bb80dc03e001aa 0xfffe2ff33fc00ffe 0xffff8bfccff003ff

def z800 : W := mkw 0x1337bc0005db6000 0x04cdef000176d800 0xd3fffc0001fff001 0xf4ffff00007ffc00

def z801 : W := mkw 0x09c162cf0a368dc3 0x027058b3c28da370 0xefc1e38f0c3f8f03 0x3bf078e3c30fe3c0

def z802 : W := mkw 0x0b2f61bf05b68b6b 0x02cbd86fc16da2da 0x103fe03f01ff803d 0x840ff80fc07fe00f

def z803 : W := mkw 0x01c122450a328cc2 0x00704891428ca330 0xefc1e3cf0e3f8fc3 0x7bf078f3c38fe3f0

def z804 : W := mkw 0x041cd1acc52c5b30 0xc107346b314b16cc 0xfc3dd38ccd3c7701 0xbf0f74e3334f1dc0

def z805 : W := mkw 0x03bbbb72a0000000 0x00eeeedca8000000 0x53fe3c7ff0000003 0xd4ff8f1ffc000000

def z806 : W := mkw 0x888843ff50249fff 0xa22210ffd40927ff 0x080003fff0000ffe 0x020000fffc0003ff

def z807 : W := mkw 0x848843fff0249b76 0xe12210fffc0926dd 0x080003fff0000ffe 0x020000fffc0003ff

def z808 : W := mkw 0x09c162ca0a160581 0x027058b282858160 0xafc1c3800e3f8700 0x2bf070e0038fe1c0

def z809 : W := mkw 0x03bbfbfaa0000000 0x00eefefea8000000 0x9bffffdff0000001 0x66fffff7fc000000

def z810 : W := mkw 0x0a7a9935aa368dc3 0x029ea64d6a8da370 0x343e1c30fe3f8fc0 0x8d0f870c3f8fe3f0

def z811 : W := mkw 0x1333bc00005b6000 0x04ccef000016d800 0x93fdfc00003ff001 0x24ff7f00000ffc00

def z812 : W := mkw 0x844404055fedfffe 0xe111010157fb7fff 0x240000000ffffffc 0x0900000003ffffff

def z813 : W := mkw 0x033bf9a880000000 0x00cefe6a20000000 0xdbfffffff0000003 0xf6fffffffc000000

def z814 : W := mkw 0x1377bc000fdb6000 0x04ddef0003f6d800 0xf7fffc7ffffff8ff 0xfdffff1ffffffe3f

def z815 : W := mkw 0x03bbfbfaa00006a8 0x00eefefea80001aa 0xdbfffffff0000703 0xf6fffffffc0001c0

def z816 : W := mkw 0x041cd1a8c50c5330 0xc107346a314314cc 0x9c3dd380cc1c7700 0x270f74e033071dc0

def z817 : W := mkw 0x03bbfbfaa0000000 0x00eefefea8000000 0xfbfffffff2238003 0xfefffffffc88e000

def z818 : W := mkw 0x09c162cf0a368dc3 0x027058b3c28da370 0xefc3ffffffff8fff 0xfbf0ffffffffe3ff

def z819 : W := mkw 0x1377bc000fdb6488 0x04ddef0003f6d922 0xf7fffc000ffff0cd 0xfdffff0003fffc33

def z820 : W := mkw 0x03bbfbfaa0000000 0x00eefefea8000000 0xdbffff8ff0000001 0xf6ffffe3fc000000

def z821 : W := mkw 0x0377b8000f1a4000 0x00ddee0003c69000 0xf7fffc000f3ff001 0xfdffff0003cffc00

def z822 : W := mkw 0x041cd1acc52c5b30 0xc107346b314b16cc 0xbc3dc3accd3c7f32 0x2f0f70eb334f1fcc

def z823 : W := mkw 0x03bbfbfaa0000488 0x00eefefea8000122 0xdbfffffff00000cf 0xf6fffffffc000033

def z824 : W := mkw 0x09c162df2a368dc3 0x027058b7ca8da370 0xefc1e3df3e3f8fc3 0x7bf078f7cf8fe3f0

def z825 : W := mkw 0x004400000f8006a8 0x0011000003e001aa 0x64023c7fffc00fff 0xd9008f1ffff003ff

def z826 : W := mkw 0x923e9d3055c9723c 0xa48fa74c15725c8f 0x103e1c30f1c0703c 0x840f870c3c701c0f

def z827 : W := mkw 0x10cc47faafdb6000 0x043311feabf6d800 0x2c0003fffffff002 0x0b0000fffffffc00

def z828 : W := mkw 0x1377bc022fdb6000 0x04ddef008bf6d800 0xf7fffc033ffff001 0xfdffff00cffffc00

def z829 : W := mkw 0x0bbbfbfaa0160101 0x02eefefea8058040 0xdbfffffff01c0003 0xf6fffffffc070000

def z830 : W := mkw 0x1377b8000f9a4000 0x04ddee0003e69000 0xf7fdf0000f3ff001 0xfdff7c0003cffc00

def z831 : W := mkw 0x09c162cf0a368dc3 0x027058b3c28da370 0x8fc1e3cf0e1f8fc2 0x63f078f3c387e3f0

def z832 : W := mkw 0x841cd1add52cdb76 0xe107346b754b36dd 0xfc3fd3fffffc7fff 0xff0ff4ffffff1fff

def z833 : W := mkw 0x9511fc8dd07ff956 0xe5447f23741ffe55 0x0001fc0ff03ff001 0x00007f03fc0ffc00

def z834 : W := mkw 0x0000040000412000 0x0000010000104800 0x60023c7ff3e3f8ff 0xd8008f1ffcf8fe3f

def z835 : W := mkw 0x1377bc000fdb6000 0x04ddef0003f6d800 0xf7ffc0000ffff000 0xfdfff00003fffc00

def z836 : W := mkw 0x1be32e530ad3a4cb 0x06f8cb94c2b4e932 0x03c22c5302c380cc 0x40f08b14c0b0e033

def z837 : W := mkw 0x09c162cf0a368dc3 0x027058b3c28da370 0x8fc1e3cf0c3f8fc3 0x23f078f3c30fe3f0

def z838 : W := mkw 0x01c122400a120480 0x0070489002848120 0xefc1e3800e3f8701 0x7bf078e0038fe1c0

def z839 : W := mkw 0x841cd1add52cdb76 0xe107346b754b36dd 0xfc3df3ffff3fffff 0xff0f7cffffcfffff

def z840 : W := mkw 0x09c162cf0a368dc3 0x027058b3c28da370 0x8fc1c3800c3f8700 0x23f070e0030fe1c0

def z841 : W := mkw 0x098162cf00368943 0x026058b3c00da250 0xefc1e3cf0c3f8f03 0x7bf078f3c30fe3c0

def z842 : W := mkw 0x1377bc000fdb6000 0x04ddef0003f6d800 0xf7fffc200ffff833 0xfdffff0803fffe0c

def z843 : W := mkw 0x03bbfbfaa0000480 0x00eefefea8000120 0xdbfffffff0000fc3 0xf6fffffffc0003f0

def z844 : W := mkw 0x904404055ffbfefe 0xa411010157feffbf 0x240000000ffffffc 0x0900000003ffffff

def z845 : W := mkw 0x0c8843ffe0249ff3 0xc32210fff80927fc 0x080003fff0000ff2 0x020000fffc0003fc

def z846 : W := mkw 0x1377bc000fdb6000 0x04ddef0003f6d800 0xf7fffc300ffff03d 0xfdffff0c03fffc0f

def z847 : W := mkw 0x09c162cf4a369dd3 0x827058b3d28da774 0xefc1e3cf0f3ffff3 0x7bf078f3c3cffffc

def z848 : W := mkw 0x0018d1acc0241910 0x8006346b30090644 0xfc3dd3accd3c7f33 0xbf0f74eb334f1fcc

def z849 : W := mkw 0x888843fff0249dd7 0xa22210fffc092775 0x080003fff0000ffe 0x020000fffc0003ff

def z850 : W := mkw 0x1377bc000fdb6000 0x04ddef0003f6d800 0xf7fffc4f0ffff003 0xfdffff13c3fffc00

def z851 : W := mkw 0x02ee03700f8006a8 0x00bb80dc03e001aa 0x9ffe03f00dc00ffe 0xa7ff80fc037003ff

def z852 : W := mkw 0x13fffbfaaf9a46a8 0x04fffefeabe691aa 0x9ffdc3800c1c0700 0x27ff70e0030701c0

def z853 : W := mkw 0x09c122430a1284c3 0x02704890c284a130 0xefc1e3c30e3f8fc3 0x7bf078f0c38fe3f0

def z854 : W := mkw 0x1377bc000fdb6000 0x04ddef0003f6d800 0xf7fffc400ffff8c3 0xfdffff1003fffe30

def z855 : W := mkw 0x02ee03700f8006a8 0x00bb80dc03e001aa 0xbffe03d00fc00ffc 0x6fff80f403f003ff

def z856 : W := mkw 0x12ee03700f9a46a8 0x04bb80dc03e691aa 0xfffe03f00fdc0ffe 0xffff80fc03f703ff

def z857 : W := mkw 0x1373bc000adb6000 0x04dcef0002b6d800 0xd3fffc0002fff001 0xf4ffff0000bffc00

def z858 : W := mkw 0x09c162df0a368dcb 0x027058b7c28da372 0xefc1e3df0e3f8fcf 0x7bf078f7c38fe3f3

def z859 : W := mkw 0x1377bc000fdb66a8 0x04ddef0003f6d9aa 0xf7fffc700fffffff 0xfdffff1c03ffffff

def z860 : W := mkw 0x09c16acf2a368dc3 0x02705ab3ca8da370 0xefc1efcf3e3f8fc3 0x7bf07bf3cf8fe3f0

def z861 : W := mkw 0x014120000a120000 0x0050480002848000 0xefc1e3800e3f8f03 0x7bf078e0038fe3c0

def z862 : W := mkw 0x09c162cf4a369dd3 0x827058b3d28da774 0xefc1f3cfce3fffc3 0x7bf07cf3f38ffff0

def z863 : W := mkw 0x03bbfbfaa0120000 0x00eefefea8048000 0xdbfffffff03f8003 0xf6fffffffc0fe000

def z864 : W := mkw 0x07a72a56652c5b30 0xc1e9ca95994b16cc 0x27c22c533d3c7f30 0x49f08b14cf4f1fcc

def z865 : W := mkw 0x82aa07755061b856 0xa0aa81dd54186e15 0xfbfe03f003e3f8fe 0xfeff80fc00f8fe3f

def z866 : W := mkw 0x001cd1a885084220 0x0007346a21421088 0xfc3dd3accd3c7f33 0xbf0f74eb334f1fcc

def z867 : W := mkw 0x0dc162cfca369dd3 0xc37058b3f28da774 0xefc1e3cfce3f8fc3 0x7bf078f3f38fe3f0

def z868 : W := mkw 0x033bf9baa0000000 0x00cefe6ea8000000 0xd3fffc3ff0000001 0xf4ffff0ffc000000

def z869 : W := mkw 0x904404055ffbf856 0xa411010157fefe15 0x240000000ffff000 0x0900000003fffc00

def z870 : W := mkw 0x1377bc000fdb6000 0x04ddef0003f6d800 0xf7fffc30fffff001 0xfdffff0c3ffffc00

def z871 : W := mkw 0x02ee03700f9206a8 0x00bb80dc03e481aa 0xfffe03f00fff8ffe 0xffff80fc03ffe3ff

def z872 : W := mkw 0x8911fc8ff077b957 0xa2447f23fc1dee55 0x0001fc0ff03ff001 0x00007f03fc0ffc00

def z873 : W := mkw 0x041cd1a8850c4320 0x4107346a214310c8 0x9c3dd3800d1c7700 0xa70f74e003471dc0

def z874 : W := mkw 0x08c042cd0a368dc3 0x023010b3428da370 0xefc1c3cc0e3f8fc3 0x7bf070f3038fe3f0

def z875 : W := mkw 0x09c162cb0a1685c3 0x027058b2c285a170 0x8fc1c3800e1f87c0 0x23f070e00387e1f0

def z876 : W := mkw 0x03bbfbfaa0000000 0x00eefefea8000000 0x1bfe3ffff0000002 0xc6ff8ffffc000000

def z877 : W := mkw 0x03bbfbfaa0000000 0x00eefefea8000000 0xdbfffffff2c000cf 0xf6fffffffcb00033

def z878 : W := mkw 0x041cd1acc52c5b30 0xc107346b314b16cc 0x9c3dd3accd3c7731 0xa70f74eb334f1dcc

def z879 : W := mkw 0x02ee03700f8006a8 0x00bb80dc03e001aa 0x1bfe03f003c00ffe 0xc6ff80fc00f003ff

def z880 : W := mkw 0x89c162cf1a368dc7 0x227058b3c68da371 0xefc1e3df3e3f8fcf 0x7bf078f7cf8fe3f3

def z881 : W := mkw 0x09c162cf0a368dc3 0x027058b3c28da370 0xefc1c3c00e3f8fc2 0x7bf070f0038fe3f0

def z882 : W := mkw 0x041cd1adc52cdb72 0xc107346b714b36dc 0xfc3ff3ffcfffffff 0xff0ffcfff3ffffff

def z883 : W := mkw 0x0bbbfbfaa0040581 0x02eefefea8010160 0xdbfffffff0000703 0xf6fffffffc0001c0

def z884 : W := mkw 0x93e32e511ad3a4ce 0x24f8cb9446b4e933 0x03c22c5332c380cc 0x40f08b14ccb0e033

def z885 : W := mkw 0x09c162cf0a368dc3 0x027058b3c28da370 0xefc3efdf3e3f8fc3 0x7bf0fbf7cf8fe3f0

def z886 : W := mkw 0x041cd1a8c50c5330 0xc107346a314314cc 0xdc3dd3accd1c7733 0xb70f74eb33471dcc

def z887 : W := mkw 0x03b3ba5220000000 0x00ecee9488000000 0xd3fffc7ff0000003 0xf4ffff1ffc000000

def z888 : W := mkw 0x02ee03700f8006a8 0x00bb80dc03e001aa 0xfffe3ff00fc00fff 0xffff8ffc03f003ff

def z889 : W := mkw 0x040c41ac452c5b30 0xc103106b114b16cc 0xfc3dc3ac0d3c7f33 0xbf0f70eb034f1fcc

def z890 : W := mkw 0x13bbfbfaa01a4000 0x04eefefea8069000 0xdbfffffff01c0003 0xf6fffffffc070000

def z891 : W := mkw 0x041cd1acc52c5b30 0xc107346b314b16cc 0xfc3fffaccd3c7f33 0xff0fffeb334f1fcc

def z892 : W := mkw 0x02ee03700f8006a8 0x00bb80dc03e001aa 0xffffc3f00ffc0fff 0xfffff0fc03ff03ff

def z893 : W := mkw 0x0414d08cc52c5910 0xc1053423314b1644 0xfc3dd38ccd3c7f03 0xbf0f74e3334f1fc0

def z894 : W := mkw 0x041cd1bce52c5b30 0xc107346f394b16cc 0xfc3dd3bcfd3c7f33 0xbf0f74ef3f4f1fcc

def z895 : W := mkw 0x041cd1acc52c5b30 0xc107346b314b16cc 0xfc3fdfbcfd3c7f33 0xbf0ff7ef3f4f1fcc

def z896 : W := mkw 0x026e01200f800220 0x009b804803e00088 0xfffe03f00fc00ffe 0xffff80fc03f003ff

def z897 : W := mkw 0x036724000fd32000 0x00d9c90003f4c800 0xf7fffc000ffff001 0xfdffff0003fffc00

def z898 : W := mkw 0x03bbfbfaa0000000 0x00eefefea8000000 0xdbfffffff00008ff 0xf6fffffffc00023f

def z899 : W := mkw 0x02aa43faa0000000 0x00aa90fea8000000 0xdbfe3ffff0000003 0xf6ff8ffffc000000

def z900 : W := mkw 0x09c162cf4a369dd3 0x827058b3d28da774 0xefc3ffffff3ffff3 0xfbf0ffffffcffffc

def z901 : W := mkw 0x02ee03700f8006a8 0x00bb80dc03e001aa 0xfffc03a00fc00ffe 0xbfff00e803f003ff

def z902 : W := mkw 0x89c162cf5a369dd7 0xa27058b3d68da775 0xefc1f3ffff3fffff 0xfbf07cffffcfffff

def z903 : W := mkw 0x041cd9ace52c5b30 0xc107366b394b16cc 0xfc3ddfacfd3c7f33 0xbf0f77eb3f4f1fcc

def z904 : W := mkw 0x123e9d3005c96228 0x048fa74c0172588a 0x103e1c0001c07000 0x840f870000701c00

def z905 : W := mkw 0x863e9d30f5497234 0xe18fa74c3d525c8d 0x103e1c30f1c0703c 0x840f870c3c701c0f

def z906 : W := mkw 0x03bbfbfaa0000000 0x00eefefea8000000 0xfffffffffc3c0003 0xffffffffff0f0000

def z907 : W := mkw 0x0418d1acc02c5910 0xc106346b300b1644 0xfc3dd3accc3c7f03 0xbf0f74eb330f1fc0

def z908 : W := mkw 0x03bbfbfaa0000000 0x00eefefea8000000 0xfffffffffc000f03 0xffffffffff0003c0

def z909 : W := mkw 0x041cd1a8850c4320 0x4107346a214310c8 0xfc3dd3a00d3c7f33 0xbf0f74e8034f1fcc

def z910 : W := mkw 0x0373bc000a532000 0x00dcef000294c800 0xf7fffc000ffff001 0xfdffff0003fffc00

def z911 : W := mkw 0x03bbfbfaa0000000 0x00eefefea8000000 0x9bffffbff0000001 0xa6ffffeffc000000

def z912 : W := mkw 0x09c162cb0a1685c3 0x027058b2c285a170 0xefc1e3c30e3f87c1 0x7bf078f0c38fe1f0

def z913 : W := mkw 0x841cd1acd52c5b34 0xe107346b354b16cd 0xfc3dd3bcfd3c7f3f 0xbf0f74ef3f4f1fcf

def z914 : W := mkw 0x1377bc102fdb6000 0x04ddef040bf6d800 0xf7fffc103ffff001 0xfdffff040ffffc00

def z915 : W := mkw 0x1377bc000fdb6000 0x04ddef0003f6d800 0xb7fdfc000ffff001 0x2dff7f0003fffc00

def z916 : W := mkw 0x02bad3f880000000 0x00aeb4fe20000000 0xdbfffffff0000003 0xf6fffffffc000000

def z917 : W := mkw 0x03ab63fa00000000 0x00ead8fe80000000 0xdbfffffff0000003 0xf6fffffffc000000

def z918 : W := mkw 0x02ee03700f8006a8 0x00bb80dc03e001aa 0xfffe03800fc00ffc 0xffff80e003f003ff

def z919 : W := mkw 0x000c41ac45241b30 0x8003106b114906cc 0xfc3dd3accd3c7f33 0xbf0f74eb334f1fcc

def z920 : W := mkw 0x001cd1ac852c4900 0x0007346b214b1240 0xfc3dd3accd3c7f03 0xbf0f74eb334f1fc0

def z921 : W := mkw 0x1377bc00afdb6000 0x04ddef002bf6d800 0xf7fffc00fffff001 0xfdffff003ffffc00

def z922 : W := mkw 0x03bbfbfaa0000000 0x00eefefea8000000 0xdbfdffcff0000003 0x76ff7ff3fc000000

def z923 : W := mkw 0x0222000000000000 0x0088800000000000 0xd3fe3c7ff0000003 0xf4ff8f1ffc000000

def z924 : W := mkw 0x02ae037005000220 0x00ab80dc01400088 0xfffe03f00fc00ffe 0xffff80fc03f003ff

def z925 : W := mkw 0x02ee03700f8006a8 0x00bb80dc03e001aa 0xfffe1ff0ffc00ffe 0xffff87fc3ff003ff

def z926 : W := mkw 0x09c162ca0a160581 0x027058b282858160 0xefc1e3cf0e3f8703 0x7bf078f3c38fe1c0

def z927 : W := mkw 0x09c162ce0a360d81 0x027058b3828d8360 0xefc1e38c0e3f8f03 0x7bf078e3038fe3c0

def z928 : W := mkw 0x09c162cf0a368dc3 0x027058b3c28da370 0xefc1c38c0e3f8fc3 0x3bf070e3038fe3f0

def z929 : W := mkw 0x800004015041b056 0xa000010054106c15 0x40023c7ff3c3f0ff 0xd0008f1ffcf0fc3f

def z930 : W := mkw 0x041cd1acc52c5b30 0xc107346b314b16cc 0xfc3fd3fccd3c7f33 0xff0ff4ff334f1fcc

def z931 : W := mkw 0x1377bc000fdb6000 0x04ddef0003f6d800 0x97fffc000efff001 0x65ffff0003bffc00

def z932 : W := mkw 0x09c162cf0a368dc3 0x027058b3c28da370 0xafc1c3cf0e3f8fc2 0x2bf070f3c38fe3f0

def z933 : W := mkw 0x03bbfbfaa0000000 0x00eefefea8000000 0xfbfffffff1000833 0xfefffffffc40020c

def z934 : W := mkw 0x0014900005084000 0x0005240001421000 0xfc3dd3800d3c7f03 0xbf0f74e0034f1fc0

def z935 : W := mkw 0x02ba9b70a0000000 0x00aea6dc28000000 0xdbfe3ffff0000003 0xf6ff8ffffc000000

def z936 : W := mkw 0x0014d08c452c5910 0x80053423114b1644 0xfc3dd3accd3c7f33 0xbf0f74eb334f1fcc

def z937 : W := mkw 0x07bbfbfaa00c4100 0x41eefefea8031040 0xdbfffffff01c0003 0xf6fffffffc070000

def z938 : W := mkw 0x0337bc0005496000 0x00cdef0001525800 0xf7fffc000ffff001 0xfdffff0003fffc00

def z939 : W := mkw 0x03bbfbfaa0040100 0x00eefefea8010040 0xdffffffffc1c0703 0xf7ffffffff0701c0

def z940 : W := mkw 0x09c162cf4a369dd3 0x827058b3d28da774 0xefc1e3efce3f8ff3 0x7bf078fbf38fe3fc

def z941 : W := mkw 0x136724000fdb6000 0x04d9c90003f6d800 0xf7ffe0000ffff001 0xfdfff80003fffc00

def z942 : W := mkw 0x09c162cb0a1685c3 0x027058b2c285a170 0x8fc1e3830c1f8700 0x23f078e0c307e1c0

def z943 : W := mkw 0x09c162cf0a368dc3 0x027058b3c28da370 0xefc1e3fffe3f8fc3 0x7bf078ffff8fe3f0

def z944 : W := mkw 0x0199f3ea80000000 0x00667cfaa0000000 0xdbfffffff0000003 0xf6fffffffc000000

def z945 : W := mkw 0x1155bc000f5b6000 0x04556f0003d6d800 0xf7fdfc000f3ff001 0xfdff7f0003cffc00

def z946 : W := mkw 0x02ea03700a8006a8 0x00ba80dc02a001aa 0xdbfe03f002c00ffe 0xf6ff80fc00b003ff

def z947 : W := mkw 0x02badbfaa0000000 0x00aeb6fea8000000 0xdbfe1ffff0000002 0xf6ff87fffc000000

def z948 : W := mkw 0x1377bc000fdb6000 0x04ddef0003f6d800 0xb7ffdc000ffff000 0xadfff70003fffc00

def z949 : W := mkw 0x800004055061b856 0xa000010154186e15 0xe403fc7ffffff8ff 0xf900ff1ffffffe3f

def z950 : W := mkw 0x02ee03700f8006a8 0x00bb80dc03e001aa 0xfffe13f00fe07fff 0xffff84fc03f81fff

def z951 : W := mkw 0x1377bc000fdb6000 0x04ddef0003f6d800 0x97fdc0000c3ff000 0x25ff7000030ffc00

def z952 : W := mkw 0x02ea03700a000480 0x00ba80dc02800120 0xfffe03f00fc00ffe 0xffff80fc03f003ff

def z953 : W := mkw 0x163e9d30e5c97230 0xc58fa74c39725c8c 0x103e1c30f1c07030 0x840f870c3c701c0c

def z954 : W := mkw 0x03bbfbfaa0000000 0x00eefefea8000000 0x9bffdffff0000002 0xa6fff7fffc000000

def z955 : W := mkw 0x041cd1acc52c5b30 0xc107346b314b16cc 0x9c3dd3accd1c7f32 0xa70f74eb33471fcc

def z956 : W := mkw 0x09c162cf0a368dc3 0x027058b3c28da370 0xafc1e38f0e3f8fc1 0x2bf078e3c38fe3f0

def z957 : W := mkw 0x001cd1ac052c4b20 0x0007346b014b12c8 0xfc3dd3ac0d3c7f33 0xbf0f74eb034f1fcc

def z958 : W := mkw 0x1155b4000fdb6000 0x04556d0003f6d800 0xf7fdf0000ffff001 0xfdff7c0003fffc00

def z959 : W := mkw 0x123e9d30a5c96228 0x048fa74c2972588a 0x103e1c30f1c0703c 0x840f870c3c701c0f

def z960 : W := mkw 0x09c162cf0a368dc3 0x027058b3c28da370 0xcfc1e3cf0c3f8703 0x73f078f3c30fe1c0

def z961 : W := mkw 0x89c162cf5a369dd7 0xa27058b3d68da775 0xefc3fffffe3f8fff 0xfbf0ffffff8fe3ff

def z962 : W := mkw 0x863e9530d5c9723c 0xe18fa54c35725c8f 0x103e1c30f1c0703c 0x840f870c3c701c0f

def z963 : W := mkw 0x1377bc000fdb6000 0x04ddef0003f6d800 0xf7fffc533ffff001 0xfdffff14cffffc00

def z964 : W := mkw 0x8d11f48fd07ff957 0xe3447d23f41ffe55 0x0001fc0ff03ff001 0x00007f03fc0ffc00

def z965 : W := mkw 0x03b3faca00000000 0x00ecfeb280000000 0xdbfffffff0000003 0xf6fffffffc000000

def z966 : W := mkw 0x09c162cf0a368dc3 0x027058b3c28da370 0xefc1ffcffe3f8fc3 0x7bf07ff3ff8fe3f0

def z967 : W := mkw 0x041cd1a8850c4320 0x4107346a214310c8 0xfc3dd3accd3c7703 0xbf0f74eb334f1dc0

def z968 : W := mkw 0x800004055061b856 0xa000010154186e15 0x00023c7ff3c3f8fe 0xc0008f1ffcf0fe3f

def z969 : W := mkw 0x03bbfbfaa0084000 0x00eefefea8021000 0xdbfffffff03c7003 0xf6fffffffc0f1c00

def z970 : W := mkw 0x03b3fadaa0000000 0x00ecfeb6a8000000 0xd3fffc5ff0000001 0xf4ffff17fc000000

def z971 : W := mkw 0x01c162ce0a360900 0x007058b3828d8240 0xefc1e3cf0e3f8f03 0x7bf078f3c38fe3c0

def z972 : W := mkw 0x02ee03700f8006a8 0x00bb80dc03e001aa 0xbffe03b00fc00ffc 0xafff80ec03f003ff

def z973 : W := mkw 0x0377b0000f9a4000 0x00ddec0003e69000 0xf7fff0000ffff001 0xfdfffc0003fffc00

def z974 : W := mkw 0x02ee0370af8006a8 0x00bb80dc2be001aa 0xfffe03f0ffc00ffe 0xffff80fc3ff003ff

def z975 : W := mkw 0x02ae0370058006a8 0x00ab80dc016001aa 0xdbfe03f001c00ffe 0xf6ff80fc007003ff

def z976 : W := mkw 0x041cd1aee52c5b30 0xc107346bb94b16cc 0xfc3dd3affd3c7f33 0xbf0f74ebff4f1fcc

def z977 : W := mkw 0x041c9124452c5b30 0xc1072449114b16cc 0xfc3dd3a00d3c7f33 0xbf0f74e8034f1fcc

def z978 : W := mkw 0x848843fdd0249ffe 0xe12210ff740927ff 0x080003fff0000ffe 0x020000fffc0003ff

def z979 : W := mkw 0x09c162cb0a1685c3 0x027058b2c285a170 0xefc1e3c30e1f8fc2 0x7bf078f0c387e3f0

def z980 : W := mkw 0x041cd1acc52c5b30 0xc107346b314b16cc 0x9c3dc3800c3c7700 0x270f70e0030f1dc0

def z981 : W := mkw 0x041cd1ac852c4b20 0x4107346b214b12c8 0xfc3dd38c0d3c7f03 0xbf0f74e3034f1fc0

def z982 : W := mkw 0x1377bc000fdb6220 0x04ddef0003f6d888 0xf7fffc000fffff31 0xfdffff0003ffffcc

def z983 : W := mkw 0x001c912445285a30 0x80072449114a168c 0xfc3dd3accd3c7f33 0xbf0f74eb334f1fcc

def z984 : W := mkw 0x026e01200f8006a8 0x009b804803e001aa 0xfffe03a00fc00ffe 0xffff80e803f003ff

def z985 : W := mkw 0x1337bc00055b6000 0x04cdef000156d800 0xf7fffc000d3ff001 0xfdffff00034ffc00

def z986 : W := mkw 0x041cd1acc52c5b30 0xc107346b314b16cc 0xfc3dffaffd3c7f33 0xbf0f7febff4f1fcc

def z987 : W := mkw 0x800004055065b956 0xa000010154196e55 0x64023c7fffffffff 0xd9008f1fffffffff

def z988 : W := mkw 0x02ee03700f8006a8 0x00bb80dc03e001aa 0xfffe23ff0fc00fff 0xffff88ffc3f003ff

def z989 : W := mkw 0x1be32e420ad32481 0x06f8cb9082b4c920 0x03c22c0002c38000 0x40f08b0000b0e000

def z990 : W := mkw 0x09c162cf0ab68dcb 0x027058b3c2ada372 0xefc1e3cf0eff8fcf 0x7bf078f3c3bfe3f3

def z991 : W := mkw 0x041cd1acc52c5b30 0xc107346b314b16cc 0xfc3fd3accffc7f33 0xff0ff4eb33ff1fcc

def z992 : W := mkw 0x1377bc000fdb6000 0x04ddef0003f6d800 0xf7fde0000ffff001 0x7dff780003fffc00

def z993 : W := mkw 0x03b3facaa0000000 0x00ecfeb2a8000000 0xdbffffcff0000003 0xf6fffff3fc000000

def z994 : W := mkw 0x09c162cb0a1685c3 0x027058b2c285a170 0xcfc1e3cf0e1f87c3 0x73f078f3c387e1f0

def z995 : W := mkw 0x0414d08c452c5b30 0xc1053423114b16cc 0xfc3dd38c0d3c7f33 0xbf0f74e3034f1fcc

def z996 : W := mkw 0x03bbfbfaa0000000 0x00eefefea8000000 0x13fffc7ff0000001 0xc4ffff1ffc000000

def z997 : W := mkw 0x1377bc000fdb6000 0x04ddef0003f6d800 0x97fffc000dfff001 0xa5ffff00037ffc00

def z998 : W := mkw 0x02e602400f8006a8 0x00b9809003e001aa 0xfffe03c00fc00ffe 0xffff80f003f003ff

def z999 : W := mkw 0x0c8843ffc0249ffb 0xc32210fff00927fe 0x080003ffc0000ffe 0x020000fff00003ff

def z1000 : W := mkw 0x03bbfbfaa0000000 0x00eefefea8000000 0x9bfdfffff0000003 0x26ff7ffffc000000

def z1001 : W := mkw 0x041cd1acc52c5b30 0xc107346b314b16cc 0x9c3dd3accc3c7f33 0x270f74eb330f1fcc

def z1002 : W := mkw 0x03bbbb7000000000 0x00eeeedc00000000 0xdbfffffff0000003 0xf6fffffffc000000

def z1003 : W := mkw 0x1377bc000fdb6000 0x04ddef0003f6d800 0xf7fffc700ffff003 0xfdffff1c03fffc00

def z1004 : W := mkw 0x8be326531ad3a4cf 0x22f8c994c6b4e933 0x03c22c5332c380cc 0x40f08b14ccb0e033

def z1005 : W := mkw 0x041cd1a8c50c5330 0xc107346a314314cc 0x9c3dc3800d1c7730 0x270f70e003471dcc

def z1006 : W := mkw 0x014160880a160100 0x0050582202858040 0xefc1e3800e3f8701 0x7bf078e0038fe1c0

def z1007 : W := mkw 0x127694000fdb6000 0x049da50003f6d800 0xf7ffd0000ffff001 0xfdfff40003fffc00

def z1008 : W := mkw 0x9911fc8f507ff957 0xa6447f23d41ffe55 0x0001fc0ff03ff001 0x00007f03fc0ffc00

def z1009 : W := mkw 0x1377bc000fdb6480 0x04ddef0003f6d920 0xf7fffc000fffffc1 0xfdffff0003fffff0

def z1010 : W := mkw 0x1377bc000fdb6000 0x04ddef0003f6d800 0x13fffc0003fff001 0xc4ffff0000fffc00

def z1011 : W := mkw 0x03bbfbfaa0800008 0x00eefefea8200002 0xdbfffffff0c0000f 0xf6fffffffc300003

def z1012 : W := mkw 0x03bbfbfaa0000000 0x00eefefea8000000 0xdbfdffaff0000003 0xb6ff7febfc000000

def z1013 : W := mkw 0x041cd1acc52c5b30 0xc107346b314b16cc 0xfc3dd3eccf3c7ff3 0xff0f74fb33cf1ffc

def z1014 : W := mkw 0x041cd1acc52c5b30 0xc107346b314b16cc 0xfc3df3efcd3c7f33 0xff0f7cfbf34f1fcc

def z1015 : W := mkw 0x02ee03700f8006a8 0x00bb80dc03e001aa 0xfffe03ffffc00ffe 0xffff80fffff003ff

def z1016 : W := mkw 0x9be32e431ad3a4c7 0x26f8cb90c6b4e931 0x03c22c5332c380cc 0x40f08b14ccb0e033

def z1017 : W := mkw 0x13e32e522ad32488 0x04f8cb948ab4c922 0x03c22c5332c380cc 0x40f08b14ccb0e033

def z1018 : W := mkw 0x041cd1acc52c5b30 0xc107346b314b16cc 0xfc3dd3fffd3c7f33 0xbf0f74ffff4f1fcc

def z1019 : W := mkw 0x041cd1acc52c5b30 0xc107346b314b16cc 0xdc3dd3accc3c7703 0xb70f74eb330f1dc0

def z1020 : W := mkw 0x800004055061b856 0xa000010154186e15 0x00023c7ff3e3f0fd 0xc0008f1ffcf8fc3f

def z1021 : W := mkw 0x027694000fc96000 0x009da50003f25800 0xf7fffc000ffff001 0xfdffff0003fffc00

def z1022 : W := mkw 0x02ee03700f8006a8 0x00bb80dc03e001aa 0xbffc03f00fc00ffe 0x2fff00fc03f003ff

def z1023 : W := mkw 0x02e602400f800480 0x00b9809003e00120 0xfffe03f00fc00ffe 0xffff80fc03f003ff

def z1024 : W := mkw 0x03bbfbfaa00006a8 0x00eefefea80001aa 0xfbfffffff3c00fff 0xfefffffffcf003ff

def z1025 : W := mkw 0x1be32e532ad3a4c3 0x06f8cb94cab4e930 0x03c22c5332c380c0 0x40f08b14ccb0e030

def z1026 : W := mkw 0x89c162cf5a369dd7 0xa27058b3d68da775 0xefc1e3cf0e3f8fff 0x7bf078f3c38fe3ff

def z1027 : W := mkw 0x944404055ffffb76 0xe511010157fffedd 0x240000000ffffffc 0x0900000003ffffff

def z1028 : W := mkw 0x800004055061b856 0xa000010154186e15 0xec023fffffe3ffff 0xfb008ffffff8ffff

def z1029 : W := mkw 0x03bbfbfaa0000000 0x00eefefea8000000 0xfbfffffff20008c3 0xfefffffffc800230

def z1030 : W := mkw 0x09c162cf0a368dc3 0x027058b3c28da370 0xefc1f3cf0f3fffc3 0xfbf07cf3c3cffff0

def z1031 : W := mkw 0x163e9d2085c96220 0x458fa74821725888 0x103e1c0001c07000 0x840f870000701c00

def z1032 : W := mkw 0x0c1cd1afc52cdb73 0xc307346bf14b36dc 0xfc3dd3afcd3c7f33 0xbf0f74ebf34f1fcc

def z1033 : W := mkw 0x09c162cf0a368dc3 0x027058b3c28da370 0xefc3e3ff0e3f8fc3 0xfbf0f8ffc38fe3f0

def z1034 : W := mkw 0x1377bc000fdb6000 0x04ddef0003f6d800 0xb7ffec000ffff000 0x6dfffb0003fffc00

def z1035 : W := mkw 0x00cc03600f8006a8 0x003300d803e001aa 0xfffc03e00fc00ffe 0xffff00f803f003ff

def z1036 : W := mkw 0x1377bc000fdb6000 0x04ddef0003f6d800 0xf7fffc500ffff0cd 0xfdffff1403fffc33

def z1037 : W := mkw 0x0333f88aa0000000 0x00ccfe22a8000000 0xd3fffc7ff0000003 0xf4ffff1ffc000000

def z1038 : W := mkw 0x1377bc000fdb6000 0x04ddef0003f6d800 0xf7fffc000ffff8fd 0xfdffff0003fffe3f

def z1039 : W := mkw 0x89c162cf5a369dd7 0xa27058b3d68da775 0xefc3e3ffffff8fff 0xfbf0f8ffffffe3ff

def z1040 : W := mkw 0x1373bc000a5b6000 0x04dcef000296d800 0xf7fffc000e3ff001 0xfdffff00038ffc00

def z1041 : W := mkw 0x041c9120c5085230 0xc10724483142148c 0xfc3dd3a0cd3c7f33 0xbf0f74e8334f1fcc

def z1042 : W := mkw 0x1333bc00005b6000 0x04ccef000016d800 0xf3fffc0003fff001 0xfcffff0000fffc00

def z1043 : W := mkw 0x00c042cd0a248dc2 0x003010b342892370 0xefc1e3cf0e3f8fc3 0x7bf078f3c38fe3f0

def z1044 : W := mkw 0x03bbfbfaa0000228 0x00eefefea800008a 0xdbfffffff000003f 0xf6fffffffc00000f

def z1045 : W := mkw 0x041cd1acc52c5b30 0xc107346b314b16cc 0xfc3fd3bccdfc7f3f 0xbf0ff4ef337f1fcf

def z1046 : W := mkw 0x033bf9aaa0000000 0x00cefe6aa8000000 0xdbffffaff0000003 0xf6ffffebfc000000

def z1047 : W := mkw 0x09c162cf0a368dc3 0x027058b3c28da370 0xefc3e3df0eff8fcf 0x7bf0f8f7c3bfe3f3

def z1048 : W := mkw 0x041cd1adc52cdb72 0xc107346b714b36dc 0xfc3dd3efcd3c7ff3 0xbf0f74fbf34f1ffc

def z1049 : W := mkw 0x09c162cf0a368dc3 0x027058b3c28da370 0xefc1e3ff0e3f8fff 0x7bf078ffc38fe3ff

def z1050 : W := mkw 0x09c162ca0a160581 0x027058b282858160 0x8fc1e3800e1f8700 0x63f078e00387e1c0

def z1051 : W := mkw 0x1377bc000fdb6000 0x04ddef0003f6d800 0xf7fdfc000e3ff001 0x7dff7f00038ffc00

def z1052 : W := mkw 0x1377bc000fdb6000 0x04ddef0003f6d800 0xf7fffc0ffffff001 0xfdffff03fffffc00

def z1053 : W := mkw 0x89c162cf5a369dd7 0xa27058b3d68da775 0xefc1e3cffe3f8fc3 0x7bf078f3ff8fe3f0

def z1054 : W := mkw 0x1377bc000fdb6000 0x04ddef0003f6d800 0xf7fdd0000ffff001 0xbdff740003fffc00

def z1055 : W := mkw 0x09c162ca0a160581 0x027058b282858160 0x8fc1e3800c3f8701 0x23f078e0030fe1c0

def z1056 : W := mkw 0x09c162cf0a368dc3 0x027058b3c28da370 0xefc3ffcf0e3f8fc3 0xfbf0fff3c38fe3f0

def z1057 : W := mkw 0x09c122450a368dc3 0x02704891428da370 0xefc1e3c00e3f8fc3 0x7bf078f0038fe3f0

def z1058 : W := mkw 0x09c162cf4a369dd3 0x827058b3d28da774 0xefc3f3ffcfffffff 0xfbf0fcfff3ffffff

def z1059 : W := mkw 0x884404055ff7bfff 0xa211010157fdefff 0x240000000ffffffc 0x0900000003ffffff

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z8,z4,z5,z6]),(0,[z9,z2,z3,z8,z4,z5,z6]),(0,[z2,z10,z3,z8,z4,z5,z6])],[(0,[z11,z3,z8,z12,z4,z5,z6]),(0,[z13,z2,z14,z8,z4,z5,z6]),(1,[z2,z3,z15,z4,z5,z6]),(0,[z2,z3,z8,z4,z16,z5,z6]),(0,[z2,z3,z8,z4,z5,z17,z6]),(0,[z18,z2,z3,z8,z4,z19,z6]),(0,[z2,z3,z20,z4,z21,z5,z6]),(0,[z22,z2,z3,z8,z4,z5,z6])],[(0,[z23,z2,z3,z8,z4,z24,z6]),(0,[z25,z2,z3,z8,z4,z5,z6])],[(1,[z11,z3,z8,z12,z5,z6]),(0,[z2,z3,z8,z26,z4,z5,z6])],[(0,[z2,z3,z27,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z28,z5,z6]),(0,[z2,z3,z29,z8,z4,z5,z6])],[(0,[z30,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z31,z5,z6]),(0,[z32,z2,z3,z8,z4,z5,z6])],[(0,[z33,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z34,z4,z5,z6]),(0,[z2,z3,z8,z4,z35,z5,z6]),(0,[z36,z2,z3,z8,z4,z5,z6])],[]],
   [[(1,[z2,z14,z8,z4,z5,z6]),(0,[z37,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z38,z6]),(0,[z2,z3,z8,z4,z5,z6,z39]),(0,[z40,z2,z3,z8,z4,z5,z6])],[(0,[z41,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z4,z5,z42,z6,z43])],[(0,[z2,z3,z44,z8,z4,z5,z6]),(0,[z45,z2,z3,z8,z4,z5,z6])],[(0,[z46,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z47,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z6,z48]),(0,[z2,z3,z8,z49,z4,z5,z6])],[],[(0,[z50,z2,z3,z8,z4,z5,z6]),(0,[z51,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z52,z6]),(0,[z2,z3,z8,z4,z5,z6,z53]),(0,[z2,z3,z8,z5,z54,z6,z55]),(0,[z56,z2,z3,z8,z4,z5,z6])],[(0,[z57,z2,z8,z4,z5,z6,z58]),(0,[z2,z3,z8,z4,z5,z6,z59]),(0,[z2,z3,z60,z20,z4,z5,z6]),(0,[z2,z3,z4,z21,z5,z61,z6])],[(0,[z62,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z63,z6]),(0,[z64,z2,z3,z8,z4,z5,z6])]],
   [[(1,[z2,z3,z8,z4,z24,z6]),(0,[z65,z2,z3,z8,z4,z66,z6]),(1,[z2,z8,z4,z5,z6,z67]),(0,[z2,z3,z8,z4,z5,z6,z68]),(0,[z69,z2,z3,z8,z4,z5,z6]),(0,[z70,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z6,z71])],[(0,[z2,z3,z20,z72,z4,z5,z6]),(0,[z2,z3,z8,z73,z4,z5,z6]),(0,[z2,z3,z8,z74,z4,z5,z6]),(0,[z2,z3,z8,z75,z76,z5,z6]),(0,[z2,z3,z8,z4,z21,z5,z6]),(0,[z77,z2,z3,z78,z4,z5,z6]),(0,[z2,z79,z3,z8,z4,z5,z6])],[(0,[z2,z3,z8,z4,z66,z5,z6]),(0,[z2,z3,z4,z5,z63,z80,z6]),(0,[z2,z3,z8,z4,z5,z6,z81])],[(0,[z82,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z83,z5,z6]),(0,[z84,z2,z3,z8,z4,z5,z6]),(0,[z2,z85,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z86,z6]),(1,[z87,z2,z3,z8,z88,z6]),(0,[z2,z3,z8,z4,z5,z89,z6])],[(0,[z2,z3,z60,z8,z76,z5,z6]),(0,[z90,z2,z3,z8,z4,z5,z6])],[(1,[z2,z91,z8,z4,z5,z6]),(0,[z2,z3,z92,z8,z4,z5,z6])],[(0,[z57,z2,z8,z4,z19,z5,z6]),(0,[z2,z3,z93,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z94,z6]),(0,[z2,z3,z8,z4,z5,z6,z95]),(0,[z2,z3,z8,z96,z4,z88,z6]),(0,[z2,z3,z8,z4,z5,z97,z6])],[(0,[z2,z3,z8,z4,z5,z6,z98]),(0,[z2,z3,z8,z99,z4,z5,z6]),(0,[z100,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z101,z6])]],
   [[(0,[z23,z102,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z6,z103]),(0,[z2,z3,z104,z8,z4,z5,z6])],[(0,[z105,z2,z3,z8,z4,z5,z6]),(0,[z13,z3,z8,z4,z5,z6,z59]),(0,[z106,z2,z3,z8,z4,z5,z6])],[(0,[z107,z2,z3,z8,z4,z5,z6]),(0,[z13,z2,z3,z8,z4,z108,z6]),(0,[z2,z3,z8,z4,z5,z6,z109]),(0,[z2,z3,z110,z8,z4,z5,z6])],[(0,[z2,z3,z8,z111,z5,z6,z55]),(0,[z2,z3,z8,z4,z112,z5,z6])],[(0,[z2,z3,z8,z113,z4,z5,z6]),(0,[z7,z2,z91,z8,z4,z5,z6]),(0,[z114,z2,z3,z8,z115,z5,z6]),(0,[z2,z3,z8,z4,z116,z5,z6]),(0,[z2,z3,z8,z4,z117,z6,z118]),(0,[z2,z3,z8,z4,z5,z119,z6])],[(0,[z120,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z121,z4,z5,z6])],[(1,[z2,z3,z8,z4,z122,z6]),(0,[z123,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z124,z6]),(0,[z2,z125,z3,z8,z4,z5,z6])],[(0,[z2,z3,z8,z4,z5,z6,z126]),(0,[z2,z3,z8,z4,z5,z6,z58]),(0,[z0,z2,z3,z8,z4,z21,z6]),(0,[z2,z3,z8,z4,z127,z5,z6]),(0,[z2,z3,z128,z8,z4,z5,z6])]],
   [[(1,[z129,z2,z8,z4,z5,z6]),(0,[z130,z2,z3,z8,z4,z5,z6])],[(0,[z2,z3,z8,z131,z4,z5,z6]),(0,[z2,z91,z3,z8,z4,z5,z6]),(1,[z2,z3,z8,z4,z108,z6]),(0,[z2,z3,z8,z132,z5,z6,z55]),(0,[z2,z3,z8,z4,z5,z6,z133]),(0,[z2,z3,z8,z134,z4,z5,z6])],[(0,[z135,z2,z3,z8,z4,z5,z6]),(1,[z2,z136,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z137,z5,z6])],[(0,[z138,z2,z3,z8,z4,z5,z43])],[(0,[z139,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z140,z4,z5,z6,z43]),(0,[z2,z3,z8,z4,z66,z141,z6]),(0,[z2,z142,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z143,z5,z6]),(0,[z2,z3,z8,z144,z4,z5,z6]),(1,[z2,z3,z4,z5,z145,z6]),(0,[z2,z3,z8,z4,z5,z146,z6])],[(0,[z2,z3,z8,z4,z5,z6,z147]),(0,[z2,z3,z8,z148,z4,z5,z6]),(1,[z2,z3,z8,z4,z149,z6]),(0,[z2,z3,z8,z4,z5,z150,z6]),(0,[z2,z3,z8,z4,z151,z5,z6]),(0,[z152,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z6,z153])],[(0,[z57,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z154,z5,z6]),(0,[z2,z3,z8,z155,z4,z5,z6]),(1,[z2,z3,z156,z4,z5,z6]),(0,[z2,z157,z3,z8,z4,z5,z6])],[(0,[z2,z158,z3,z8,z4,z66,z6]),(0,[z2,z3,z8,z4,z5,z159,z6])]],
   [[(0,[z160,z11,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z161,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z6,z162])],[(0,[z2,z3,z8,z4,z163,z5,z6]),(0,[z2,z3,z8,z4,z5,z164,z6]),(0,[z2,z3,z8,z4,z165,z5,z6])],[(0,[z2,z3,z166,z8,z4,z5,z6]),(0,[z160,z3,z8,z4,z111,z5,z6]),(0,[z2,z3,z8,z167,z4,z5,z6]),(0,[z168,z2,z3,z8,z4,z5,z6])],[(0,[z2,z3,z8,z4,z5,z169,z6]),(0,[z2,z3,z8,z75,z4,z5,z54])],[(0,[z2,z158,z3,z8,z4,z19,z6])],[(0,[z170,z2,z3,z8,z4,z5,z6]),(1,[z1,z3,z140,z4,z5,z6]),(0,[z2,z171,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z172,z5,z6]),(0,[z173,z2,z3,z8,z4,z5,z6]),(0,[z2,z8,z4,z5,z6,z174,z118])],[(1,[z175,z3,z72,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z176,z6]),(0,[z177,z87,z2,z3,z8,z5,z6])],[(0,[z2,z3,z8,z4,z5,z178,z6]),(0,[z2,z3,z179,z8,z4,z5,z6]),(0,[z2,z3,z180,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z181,z5,z6]),(0,[z2,z3,z8,z4,z5,z5,z6]),(0,[z114,z182,z2,z8,z4,z5,z6]),(0,[z2,z3,z8,z75,z5,z54,z6])]],
   [[(0,[z2,z3,z4,z5,z117,z6,z183])],[(1,[z184,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z185,z6]),(0,[z56,z2,z3,z8,z4,z5,z117])],[(0,[z186,z3,z27,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z187,z5,z6]),(0,[z2,z3,z8,z4,z188,z6,z118]),(1,[z0,z2,z3,z4,z61,z6]),(0,[z2,z3,z8,z4,z5,z189,z6]),(0,[z2,z190,z3,z8,z4,z5,z6])],[(0,[z191,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z6,z192]),(0,[z193,z2,z3,z8,z4,z5,z6])],[(0,[z194,z2,z3,z8,z4,z5,z6]),(0,[z195,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z196,z4,z5,z6]),(0,[z2,z3,z8,z4,z197,z5,z6])],[(0,[z2,z3,z8,z198,z4,z5,z6]),(0,[z199,z2,z3,z8,z4,z5,z6]),(0,[z184,z2,z3,z8,z4,z5,z6]),(0,[z200,z2,z3,z8,z4,z5,z6]),(0,[z201,z2,z3,z8,z4,z5,z6]),(0,[z202,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z203,z4,z5,z6])],[(0,[z2,z3,z204,z8,z4,z5,z6]),(0,[z2,z158,z8,z4,z5,z205,z6]),(0,[z2,z3,z8,z4,z5,z6,z206]),(0,[z2,z3,z8,z4,z5,z207,z6])],[(0,[z2,z3,z3,z8,z4,z5,z6]),(0,[z208,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z209,z5,z6]),(0,[z2,z3,z8,z4,z5,z6,z210]),(0,[z211,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z212,z8,z4,z5,z6]),(0,[z2,z3,z213,z8,z96,z4,z6]),(0,[z214,z2,z3,z8,z4,z5,z6])]],
   [[],[(0,[z102,z3,z27,z8,z4,z5,z6]),(0,[z2,z3,z8,z215,z4,z5,z6]),(1,[z2,z3,z8,z216,z5,z6]),(0,[z2,z3,z8,z217,z4,z5,z6]),(0,[z218,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z19,z141,z6]),(0,[z2,z3,z8,z4,z5,z219,z6]),(0,[z2,z3,z220,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z221,z6])],[],[(0,[z177,z2,z3,z8,z222,z5,z6]),(0,[z2,z3,z8,z4,z5,z223,z6]),(0,[z2,z3,z8,z4,z5,z6,z224])],[(0,[z2,z3,z8,z4,z225,z5,z6]),(0,[z226,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z115,z5,z6,z55]),(0,[z227,z2,z3,z8,z4,z5,z6]),(0,[z138,z2,z3,z8,z127,z5,z6]),(1,[z56,z2,z3,z8,z4,z118])],[(0,[z2,z3,z8,z228,z4,z5,z6]),(0,[z229,z2,z3,z8,z4,z5,z6]),(0,[z7,z2,z3,z8,z4,z80,z6]),(0,[z2,z3,z8,z4,z230,z5,z6])],[(0,[z231,z2,z3,z8,z232,z5,z6]),(0,[z2,z3,z8,z4,z233,z5,z6])],[(0,[z234,z2,z3,z8,z4,z5,z6])]],
   [[(0,[z235,z2,z3,z8,z4,z5,z6]),(0,[z236,z2,z3,z8,z4,z5,z6]),(0,[z87,z2,z3,z8,z96,z5,z6]),(0,[z2,z3,z8,z4,z5,z237,z6])],[(0,[z2,z8,z4,z5,z205,z6,z58]),(0,[z238,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z6,z239])],[(0,[z2,z3,z8,z240,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z61,z6]),(0,[z2,z3,z8,z4,z141,z5,z118])],[(0,[z23,z57,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z6,z241]),(0,[z0,z2,z3,z8,z4,z5,z6]),(0,[z242,z2,z3,z8,z4,z5,z6])],[(0,[z2,z3,z8,z4,z243,z5,z6]),(0,[z2,z3,z8,z244,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z245,z6]),(0,[z2,z3,z8,z4,z246,z5,z6])],[(0,[z247,z2,z3,z8,z4,z5,z6]),(1,[z2,z142,z248,z4,z5,z6]),(1,[z231,z2,z8,z4,z5,z58]),(0,[z2,z3,z8,z4,z5,z6,z249]),(0,[z2,z250,z3,z8,z4,z5,z6])],[(0,[z23,z2,z8,z4,z5,z205,z6]),(0,[z2,z3,z8,z4,z5,z251,z6]),(0,[z11,z2,z3,z8,z4,z5,z6]),(0,[z160,z2,z3,z8,z151,z5,z6]),(0,[z2,z3,z248,z8,z4,z5,z6]),(0,[z2,z3,z8,z252,z4,z5,z6]),(0,[z2,z3,z8,z75,z4,z5,z55]),(0,[z253,z2,z3,z8,z4,z5,z6])],[(0,[z254,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z255,z6]),(0,[z2,z3,z8,z4,z256,z5,z6]),(0,[z2,z3,z222,z4,z76,z5,z6]),(0,[z2,z3,z8,z257,z4,z5,z6]),(0,[z2,z258,z8,z4,z5,z6,z118]),(0,[z2,z3,z259,z8,z4,z5,z6])]],
   [[(0,[z2,z3,z8,z4,z260,z5,z6]),(1,[z65,z3,z8,z4,z80,z6]),(0,[z2,z261,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z262,z4,z5,z6])],[(0,[z57,z2,z158,z8,z4,z5,z6]),(0,[z65,z3,z8,z4,z5,z80,z6]),(0,[z2,z3,z8,z4,z5,z6,z263]),(0,[z2,z3,z8,z4,z5,z6,z264])],[(0,[z2,z265,z3,z8,z4,z5,z6])],[(0,[z1,z2,z3,z8,z4,z5,z6]),(0,[z2,z266,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z6,z267]),(0,[z268,z2,z3,z8,z4,z5,z6])],[(0,[z269,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z270,z6]),(0,[z2,z8,z4,z19,z5,z205,z6]),(0,[z2,z3,z271,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z141,z5,z6]),(0,[z2,z3,z8,z4,z5,z272,z6])],[(0,[z2,z273,z27,z8,z4,z5,z6]),(1,[z186,z3,z8,z4,z5,z274]),(1,[z2,z3,z8,z5,z6,z275])],[(0,[z23,z57,z2,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z276,z5,z6]),(0,[z277,z2,z3,z8,z4,z5,z6]),(0,[z160,z87,z2,z3,z8,z5,z6]),(0,[z2,z3,z8,z4,z5,z6,z67]),(0,[z2,z3,z8,z4,z278,z5,z6]),(0,[z2,z3,z8,z78,z4,z5,z6])],[(0,[z279,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z140,z20,z4,z5,z6]),(0,[z2,z3,z8,z280,z4,z5,z6]),(0,[z2,z281,z3,z8,z4,z5,z6]),(0,[z282,z2,z3,z8,z4,z5,z6]),(0,[z138,z2,z3,z8,z4,z5,z42]),(0,[z77,z2,z3,z8,z4,z5,z6])]],
   [[(0,[z2,z3,z283,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z6,z284]),(0,[z2,z3,z8,z4,z111,z5,z6]),(0,[z231,z2,z8,z4,z5,z6,z58])],[(0,[z175,z2,z3,z72,z4,z5,z6]),(0,[z11,z2,z3,z8,z151,z5,z6]),(0,[z2,z3,z20,z8,z4,z5,z42]),(0,[z2,z285,z3,z8,z4,z5,z6])],[(0,[z2,z3,z8,z4,z286,z5,z6]),(1,[z2,z158,z8,z4,z188,z6]),(1,[z287,z2,z3,z8,z5,z6]),(0,[z2,z3,z8,z4,z5,z6,z288])],[(0,[z2,z289,z3,z8,z4,z5,z6])],[(0,[z2,z3,z290,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z122,z6]),(0,[z87,z2,z3,z60,z8,z5,z6]),(0,[z291,z2,z3,z8,z4,z5,z6])],[(1,[z182,z2,z8,z115,z5,z6]),(0,[z292,z2,z3,z8,z4,z5,z6])],[(0,[z114,z2,z3,z8,z4,z5,z6]),(0,[z0,z2,z3,z8,z4,z61,z6])],[(0,[z87,z11,z2,z3,z8,z5,z6]),(0,[z2,z3,z293,z8,z4,z5,z6]),(0,[z231,z294,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z6,z295])]],
   [[(0,[z296,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z213,z4,z21,z5,z6])],[(0,[z2,z3,z8,z4,z5,z6,z297]),(0,[z2,z298,z3,z8,z4,z5,z6]),(0,[z299,z2,z3,z8,z4,z5,z6]),(0,[z300,z2,z3,z4,z5,z88,z6])],[(0,[z301,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z6,z302]),(0,[z2,z3,z8,z4,z216,z5,z6]),(0,[z2,z3,z8,z4,z132,z5,z6]),(0,[z231,z2,z3,z303,z4,z5,z6]),(0,[z304,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z305,z6]),(0,[z2,z3,z8,z4,z306,z5,z6])],[(0,[z2,z3,z8,z4,z307,z5,z6]),(0,[z231,z2,z273,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z149,z6]),(0,[z2,z3,z308,z8,z4,z5,z6]),(0,[z56,z2,z3,z8,z4,z6,z118])],[(1,[z2,z3,z309,z4,z5,z6])],[(0,[z2,z3,z8,z4,z4,z5,z6]),(0,[z310,z2,z3,z8,z4,z5,z6]),(0,[z0,z2,z3,z222,z4,z5,z6])],[(0,[z311,z2,z3,z8,z4,z5,z6]),(0,[z1,z3,z140,z8,z4,z5,z6]),(0,[z177,z2,z3,z8,z4,z5,z6])],[(0,[z2,z3,z8,z12,z4,z5,z6]),(0,[z2,z3,z8,z312,z4,z5,z6])]],
   [[(0,[z2,z3,z136,z8,z4,z5,z6]),(0,[z2,z3,z313,z8,z4,z5,z6]),(1,[z2,z8,z4,z5,z6,z174])],[(0,[z314,z2,z3,z8,z4,z5,z6]),(0,[z315,z2,z3,z8,z4,z5,z6]),(0,[z2,z273,z8,z4,z5,z205,z6])],[(0,[z2,z3,z8,z4,z316,z5,z6]),(0,[z317,z2,z3,z8,z4,z5,z6]),(0,[z13,z2,z3,z8,z4,z5,z274]),(0,[z2,z3,z8,z4,z318,z5,z6]),(0,[z2,z3,z8,z4,z5,z6,z319]),(0,[z320,z2,z3,z8,z4,z5,z6])],[(0,[z2,z3,z8,z4,z5,z321,z6]),(0,[z2,z3,z322,z8,z4,z5,z6]),(0,[z2,z3,z8,z222,z4,z5,z6]),(0,[z323,z2,z3,z8,z4,z5,z6])],[(0,[z2,z3,z8,z72,z4,z5,z6]),(0,[z1,z2,z3,z140,z4,z5,z6]),(0,[z177,z2,z3,z60,z4,z5,z6])],[(0,[z2,z158,z27,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z188,z6]),(0,[z2,z3,z20,z4,z76,z5,z6]),(0,[z324,z2,z3,z8,z4,z5,z6])],[(0,[z2,z3,z8,z4,z5,z6,z325]),(0,[z2,z3,z8,z326,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z6,z327])],[(0,[z2,z3,z8,z4,z328,z5,z6]),(0,[z2,z3,z8,z4,z5,z329,z6]),(0,[z2,z3,z330,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z331,z6])]],
   [[(0,[z2,z3,z8,z4,z5,z332,z6]),(0,[z2,z3,z333,z8,z4,z5,z6]),(0,[z231,z2,z3,z8,z4,z5,z6]),(1,[z2,z3,z8,z203,z5,z6]),(0,[z2,z3,z20,z8,z4,z5,z43])],[(0,[z2,z3,z8,z4,z334,z5,z6]),(1,[z120,z2,z3,z8,z5,z6]),(0,[z2,z3,z8,z335,z4,z5,z6]),(0,[z177,z2,z3,z8,z151,z5,z6])],[(0,[z336,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z6,z337]),(0,[z2,z3,z8,z338,z4,z5,z6]),(0,[z2,z3,z339,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z19,z5,z6]),(0,[z77,z2,z3,z340,z4,z5,z6])],[(0,[z2,z3,z8,z115,z75,z5,z6]),(0,[z341,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z342,z6])],[(0,[z343,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z80,z6]),(0,[z7,z2,z136,z8,z4,z5,z6]),(0,[z2,z3,z8,z344,z4,z5,z6]),(0,[z345,z2,z3,z8,z4,z5,z6]),(0,[z300,z2,z3,z8,z4,z5,z6])],[(0,[z346,z2,z3,z8,z4,z5,z6]),(0,[z18,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z6,z347]),(0,[z2,z3,z8,z4,z5,z348,z6])],[(0,[z2,z3,z8,z4,z5,z6,z349]),(0,[z7,z3,z8,z4,z66,z5,z6]),(0,[z182,z2,z8,z115,z4,z5,z6]),(0,[z2,z3,z8,z350,z4,z5,z6])],[(1,[z23,z57,z8,z4,z5,z6]),(0,[z120,z2,z3,z8,z5,z80,z6]),(0,[z2,z14,z3,z8,z4,z5,z6]),(0,[z182,z2,z3,z8,z115,z5,z6])]],
   [[(0,[z351,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z352,z6]),(0,[z353,z2,z3,z8,z4,z5,z6])],[(0,[z2,z3,z8,z354,z4,z5,z6]),(0,[z160,z2,z3,z8,z111,z5,z6]),(0,[z2,z3,z8,z4,z355,z5,z6]),(0,[z2,z3,z8,z4,z5,z356,z6])],[(0,[z357,z2,z3,z8,z4,z5,z6]),(0,[z23,z2,z3,z8,z4,z358,z6]),(0,[z2,z3,z8,z4,z5,z6,z359])],[(0,[z2,z3,z360,z8,z4,z5,z6]),(0,[z3,z140,z8,z72,z4,z5,z6]),(0,[z287,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z75,z4,z5,z6])],[(0,[z2,z3,z8,z5,z361,z61,z6])],[(0,[z23,z2,z27,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z362,z5,z6])],[(0,[z363,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z364,z6]),(0,[z2,z142,z248,z8,z4,z5,z6]),(0,[z365,z2,z3,z8,z4,z5,z6]),(0,[z366,z2,z3,z8,z4,z5,z6]),(0,[z367,z2,z3,z8,z4,z5,z6])],[(0,[z102,z2,z8,z4,z5,z205,z6]),(0,[z2,z3,z8,z4,z5,z368,z6])]],
   [[(0,[z2,z3,z8,z369,z4,z5,z6]),(1,[z2,z3,z78,z4,z5,z6])],[(0,[z175,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z80,z6,z118]),(0,[z114,z2,z8,z4,z132,z5,z6]),(0,[z370,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z371,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z88,z6])],[(0,[z2,z3,z8,z372,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z373,z6]),(0,[z13,z2,z3,z8,z374,z5,z6]),(0,[z2,z3,z375,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z6,z376]),(0,[z138,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z377,z4,z5,z6])],[(0,[z378,z2,z3,z8,z4,z5,z6]),(0,[z231,z2,z3,z8,z172,z5,z6]),(0,[z2,z3,z8,z4,z5,z379,z6])],[(0,[z380,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z381,z4,z5,z6]),(0,[z11,z2,z3,z8,z111,z5,z6]),(1,[z2,z3,z4,z5,z63,z6]),(0,[z382,z2,z3,z8,z4,z5,z6]),(0,[z13,z2,z29,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z383,z5,z6]),(0,[z2,z3,z20,z8,z4,z5,z6])],[(0,[z384,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z385,z5,z6]),(0,[z2,z3,z8,z4,z5,z6,z386]),(0,[z387,z2,z3,z8,z4,z5,z6])],[(0,[z2,z3,z8,z388,z4,z5,z6]),(0,[z389,z2,z3,z8,z4,z5,z6]),(0,[z160,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z390,z4,z5,z6]),(0,[z2,z3,z8,z391,z4,z5,z6]),(0,[z2,z3,z8,z303,z4,z5,z6]),(0,[z2,z3,z156,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z392,z5,z6]),(0,[z393,z2,z3,z8,z4,z5,z6]),(0,[z2,z394,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z75,z151,z5,z6])],[(0,[z2,z3,z8,z395,z4,z5,z6]),(0,[z2,z3,z8,z4,z396,z5,z6]),(0,[z397,z2,z3,z8,z4,z5,z6])]],
   [[(1,[z2,z3,z8,z4,z358,z6]),(0,[z398,z2,z3,z8,z4,z5,z6]),(0,[z399,z2,z3,z8,z4,z5,z6]),(0,[z2,z400,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z401,z6])],[(0,[z402,z2,z3,z8,z4,z5,z6]),(0,[z65,z2,z3,z8,z4,z5,z6]),(1,[z2,z3,z8,z374,z5,z6]),(1,[z114,z2,z8,z132,z5,z6]),(0,[z403,z2,z3,z8,z4,z5,z6]),(0,[z0,z87,z2,z3,z8,z4,z6])],[(0,[z2,z3,z8,z4,z404,z5,z6]),(0,[z405,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z141,z188,z6]),(1,[z406,z2,z3,z8,z4,z6]),(0,[z2,z3,z4,z21,z5,z6,z43])],[(0,[z407,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z6,z408]),(0,[z2,z3,z72,z4,z5,z6,z43]),(1,[z2,z29,z8,z4,z5,z6]),(0,[z2,z3,z8,z409,z4,z5,z6]),(0,[z2,z3,z410,z8,z4,z5,z6])],[(0,[z2,z3,z8,z4,z411,z5,z6]),(0,[z2,z3,z8,z4,z5,z6,z412]),(0,[z2,z3,z8,z4,z413,z5,z6])],[(0,[z2,z3,z8,z414,z4,z5,z6]),(0,[z186,z2,z3,z8,z4,z5,z274]),(0,[z2,z3,z20,z4,z5,z42,z6]),(0,[z2,z415,z3,z8,z4,z5,z6])],[(0,[z57,z3,z27,z8,z4,z5,z6]),(0,[z416,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z6,z417]),(0,[z2,z3,z8,z4,z418,z5,z6])],[(0,[z3,z8,z4,z66,z5,z80,z6]),(0,[z2,z3,z419,z8,z4,z5,z6]),(0,[z231,z2,z3,z8,z4,z5,z205]),(0,[z2,z420,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z6,z421])]],
   [[(0,[z422,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z6,z423]),(0,[z424,z2,z3,z8,z4,z5,z6]),(0,[z425,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z426,z8,z4,z5,z6]),(1,[z2,z3,z8,z5,z361,z6])],[(0,[z2,z427,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z141,z80,z6]),(0,[z428,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z429,z5,z6])],[(0,[z2,z3,z8,z232,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z6,z430]),(0,[z2,z3,z431,z8,z4,z5,z6]),(0,[z177,z2,z3,z4,z76,z5,z6]),(0,[z2,z3,z8,z4,z432,z5,z6]),(0,[z2,z3,z8,z4,z5,z6,z433])],[(0,[z2,z3,z8,z434,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z435,z6])],[(0,[z23,z186,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z8,z4,z5,z6]),(0,[z138,z2,z3,z20,z4,z5,z6])],[(0,[z436,z2,z3,z8,z4,z5,z6]),(0,[z437,z2,z3,z8,z4,z5,z6]),(0,[z87,z2,z3,z8,z4,z5,z6])],[(0,[z2,z3,z8,z438,z4,z5,z6]),(1,[z13,z3,z8,z4,z5,z59])],[(0,[z2,z3,z8,z4,z5,z439,z6]),(0,[z2,z3,z4,z5,z145,z88,z6]),(0,[z77,z2,z3,z8,z5,z6,z55])]],
   [[(0,[z440,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z60,z222,z4,z5,z6]),(0,[z2,z3,z8,z441,z4,z5,z6])],[(0,[z2,z3,z8,z4,z5,z6,z442]),(0,[z443,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z444,z8,z4,z5,z6])],[(0,[z175,z2,z3,z140,z4,z5,z6]),(0,[z2,z3,z8,z445,z4,z5,z6]),(0,[z2,z3,z8,z4,z446,z5,z6]),(0,[z87,z2,z3,z8,z4,z151,z6])],[(0,[z2,z3,z8,z4,z447,z5,z6]),(0,[z2,z3,z8,z4,z448,z5,z6]),(0,[z2,z3,z8,z4,z5,z449,z6]),(0,[z2,z294,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z6,z450])],[(0,[z175,z1,z3,z8,z4,z5,z6]),(0,[z231,z2,z3,z8,z4,z149,z6]),(0,[z2,z3,z8,z4,z451,z5,z6]),(0,[z2,z3,z8,z4,z5,z6,z452]),(0,[z2,z3,z8,z96,z151,z5,z6]),(0,[z2,z453,z3,z8,z4,z5,z6])],[(0,[z454,z2,z3,z8,z4,z5,z6]),(0,[z123,z2,z3,z26,z4,z5,z6]),(0,[z2,z455,z3,z8,z4,z5,z6]),(0,[z456,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z457,z5,z6])],[(0,[z114,z2,z3,z8,z132,z5,z6]),(0,[z2,z3,z60,z8,z222,z5,z6])],[(0,[z2,z3,z8,z458,z4,z5,z6]),(0,[z2,z3,z459,z8,z4,z5,z6])]],
   [[(0,[z2,z3,z8,z460,z4,z5,z6]),(0,[z2,z3,z8,z461,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z462,z6]),(0,[z7,z65,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z463,z5,z6]),(0,[z2,z158,z3,z8,z4,z5,z6]),(0,[z0,z2,z3,z20,z4,z5,z6]),(0,[z2,z3,z464,z8,z4,z5,z6])],[(0,[z2,z3,z8,z465,z4,z5,z6]),(0,[z2,z3,z466,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z117,z6])],[(0,[z2,z3,z467,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z468,z6]),(0,[z2,z3,z8,z4,z5,z6,z469])],[(0,[z470,z2,z3,z8,z4,z5,z6]),(0,[z160,z2,z3,z8,z12,z5,z6]),(0,[z2,z142,z3,z26,z4,z5,z6]),(0,[z2,z3,z248,z20,z4,z5,z6]),(0,[z231,z2,z8,z4,z19,z5,z6]),(0,[z406,z2,z3,z8,z4,z5,z6]),(0,[z2,z471,z3,z8,z4,z5,z6]),(0,[z287,z2,z3,z8,z5,z61,z6]),(0,[z2,z3,z8,z4,z5,z472,z6]),(0,[z2,z3,z8,z473,z4,z5,z6])],[(0,[z2,z3,z474,z8,z4,z5,z6]),(0,[z2,z3,z475,z8,z4,z5,z6])],[(0,[z476,z2,z3,z8,z4,z5,z6]),(0,[z477,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z6,z55])],[(0,[z2,z3,z478,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z479,z6]),(0,[z2,z3,z8,z4,z5,z6,z174])],[(0,[z2,z3,z480,z8,z4,z5,z6]),(0,[z2,z3,z8,z12,z5,z6,z55]),(0,[z231,z2,z3,z8,z4,z385,z6]),(0,[z2,z273,z3,z8,z4,z5,z205]),(0,[z2,z481,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z482,z4,z5,z6])]],
   [[(0,[z13,z2,z3,z8,z483,z5,z6]),(0,[z18,z2,z8,z4,z19,z5,z6]),(0,[z231,z184,z3,z8,z4,z5,z6]),(0,[z2,z3,z222,z4,z21,z5,z6]),(0,[z2,z3,z8,z134,z5,z117,z6])],[(0,[z57,z102,z2,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z484,z6]),(0,[z2,z3,z8,z485,z4,z5,z6])],[(0,[z2,z3,z8,z4,z5,z486,z6]),(0,[z487,z2,z3,z8,z4,z5,z6])],[(0,[z488,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z66,z6,z118]),(0,[z18,z2,z3,z8,z4,z188,z6]),(0,[z2,z3,z8,z222,z5,z6,z55])],[(0,[z2,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z489,z6]),(0,[z138,z2,z3,z4,z5,z6,z43])],[(0,[z490,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z491,z6]),(0,[z2,z3,z8,z4,z5,z492,z6]),(0,[z2,z3,z493,z8,z4,z5,z6]),(0,[z494,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z495,z5,z6]),(0,[z2,z3,z8,z4,z5,z6,z496]),(0,[z497,z2,z3,z8,z4,z5,z6])],[(0,[z102,z2,z27,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z498,z5,z6]),(0,[z11,z2,z3,z8,z12,z5,z6]),(0,[z2,z3,z8,z499,z4,z5,z6]),(0,[z182,z2,z3,z8,z132,z5,z6]),(0,[z2,z500,z3,z8,z4,z5,z6]),(0,[z2,z3,z501,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z502,z5,z6])],[(1,[z2,z3,z8,z483,z5,z6]),(0,[z2,z3,z503,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z504,z6]),(0,[z0,z2,z3,z8,z96,z4,z6])]],
   [[(0,[z23,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z505,z5,z6])],[(0,[z2,z3,z8,z75,z111,z5,z6]),(0,[z2,z248,z8,z26,z4,z5,z6]),(0,[z182,z2,z3,z8,z4,z5,z6])],[(0,[z18,z2,z3,z8,z4,z80,z6])],[(0,[z506,z2,z3,z8,z4,z5,z6]),(1,[z7,z3,z8,z4,z66,z6]),(0,[z2,z3,z8,z483,z4,z5,z6]),(0,[z507,z2,z3,z8,z4,z5,z6]),(0,[z508,z2,z3,z8,z4,z5,z6])],[(1,[z107,z2,z3,z4,z5,z6])],[(0,[z2,z3,z8,z4,z509,z5,z6]),(0,[z2,z3,z340,z8,z4,z5,z6])],[(0,[z2,z3,z8,z4,z24,z5,z6]),(0,[z2,z510,z3,z8,z4,z5,z6])],[(0,[z2,z27,z8,z4,z5,z6,z58]),(0,[z2,z3,z8,z4,z5,z511,z6]),(0,[z13,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z512,z6]),(1,[z18,z2,z8,z4,z19,z6]),(0,[z2,z3,z4,z76,z5,z6,z43]),(0,[z2,z3,z213,z8,z4,z21,z6]),(0,[z2,z3,z8,z513,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z6,z514])]],
   [[(0,[z515,z2,z3,z8,z4,z5,z6]),(0,[z516,z2,z3,z8,z4,z5,z6]),(0,[z123,z2,z3,z248,z4,z5,z6]),(0,[z2,z3,z20,z26,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z517,z6]),(0,[z0,z2,z3,z4,z5,z6,z43]),(0,[z2,z3,z8,z4,z518,z5,z6]),(0,[z2,z3,z8,z4,z5,z6,z183])],[(0,[z519,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z6,z275])],[],[(0,[z2,z3,z8,z520,z4,z5,z6]),(0,[z521,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z6,z522]),(0,[z2,z3,z248,z4,z5,z6,z43]),(0,[z2,z3,z8,z75,z132,z5,z6]),(0,[z523,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z524,z5,z6]),(0,[z525,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z141,z5,z117])],[(0,[z526,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z527,z5,z6]),(0,[z2,z3,z8,z4,z5,z528,z6]),(0,[z529,z2,z3,z8,z4,z5,z6])],[(0,[z530,z2,z3,z8,z4,z5,z6]),(1,[z77,z2,z3,z8,z5,z55])],[(0,[z2,z3,z8,z4,z5,z6,z531]),(0,[z2,z142,z3,z248,z4,z5,z6]),(0,[z2,z3,z8,z4,z532,z5,z6]),(0,[z533,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z6,z43]),(0,[z2,z3,z8,z4,z141,z117,z6])],[(0,[z534,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z535,z6]),(0,[z2,z3,z8,z536,z4,z5,z6]),(0,[z537,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z145,z6]),(0,[z538,z2,z3,z8,z4,z5,z6])]],
   [[(0,[z2,z3,z8,z4,z19,z6,z118]),(1,[z177,z2,z3,z76,z5,z6]),(0,[z2,z3,z8,z4,z76,z5,z6])],[(0,[z539,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z60,z8,z4,z5,z6]),(0,[z177,z2,z3,z8,z76,z5,z6]),(0,[z87,z2,z3,z8,z75,z5,z6])],[(0,[z2,z3,z8,z4,z540,z5,z6]),(1,[z160,z3,z8,z111,z5,z6])],[(0,[z2,z3,z8,z4,z5,z541,z6]),(0,[z542,z2,z3,z8,z4,z5,z6])],[(0,[z543,z2,z3,z8,z4,z5,z6]),(0,[z2,z544,z3,z8,z4,z5,z6])],[(0,[z2,z3,z8,z545,z4,z5,z6]),(0,[z231,z2,z3,z8,z4,z5,z58])],[(0,[z231,z23,z2,z8,z4,z5,z6]),(0,[z2,z546,z3,z8,z4,z5,z6]),(0,[z65,z2,z3,z8,z4,z80,z6]),(0,[z2,z3,z8,z4,z547,z5,z6]),(0,[z77,z2,z3,z8,z75,z5,z6]),(0,[z2,z258,z3,z8,z4,z5,z6])],[(0,[z548,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z549,z6]),(0,[z2,z3,z8,z4,z5,z550,z6]),(0,[z551,z2,z3,z8,z4,z5,z6])]],
   [[(0,[z2,z3,z8,z552,z4,z5,z6]),(0,[z553,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z6,z554]),(0,[z2,z3,z8,z4,z5,z555,z6]),(0,[z56,z2,z3,z8,z4,z5,z118]),(0,[z2,z3,z8,z4,z5,z6,z118])],[(0,[z2,z3,z556,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z557,z5,z6])],[(0,[z558,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z6,z559]),(0,[z2,z3,z560,z8,z4,z5,z6])],[(0,[z2,z3,z8,z4,z561,z5,z6]),(1,[z123,z2,z26,z4,z5,z6]),(0,[z2,z273,z3,z8,z4,z5,z6])],[(0,[z562,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z26,z4,z5,z6,z43]),(0,[z2,z3,z60,z8,z151,z5,z6]),(1,[z138,z2,z3,z4,z5,z43]),(0,[z77,z2,z3,z8,z4,z5,z54])],[(0,[z2,z3,z563,z8,z4,z5,z6]),(0,[z406,z2,z3,z8,z4,z76,z6])],[(0,[z2,z158,z8,z4,z5,z188,z6])],[(0,[z2,z3,z564,z8,z4,z5,z6]),(0,[z177,z0,z2,z3,z4,z5,z6]),(0,[z565,z2,z3,z8,z4,z5,z6])]],
   [[(0,[z2,z3,z566,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z567,z5,z6]),(0,[z2,z3,z8,z4,z5,z568,z6]),(0,[z2,z3,z8,z4,z569,z5,z6]),(1,[z2,z273,z8,z4,z5,z205])],[(0,[z2,z570,z3,z8,z4,z5,z6]),(1,[z2,z3,z8,z172,z5,z6]),(0,[z571,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z6,z572])],[(0,[z2,z3,z8,z4,z5,z6,z6]),(0,[z2,z3,z8,z4,z5,z6,z573])],[(0,[z574,z2,z3,z8,z4,z5,z6]),(0,[z575,z2,z3,z8,z4,z5,z6]),(0,[z2,z8,z4,z5,z6,z67,z59]),(0,[z2,z3,z8,z4,z576,z5,z6])],[(0,[z129,z2,z8,z4,z5,z6,z59]),(0,[z577,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z96,z4,z5,z6]),(1,[z2,z3,z8,z134,z5,z6])],[(0,[z2,z3,z8,z4,z5,z274,z6]),(0,[z2,z3,z8,z4,z5,z578,z6]),(0,[z87,z2,z3,z8,z5,z6,z55])],[(0,[z579,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z12,z75,z5,z6]),(0,[z3,z8,z4,z5,z274,z6,z59]),(0,[z2,z158,z3,z8,z4,z188,z6]),(0,[z231,z2,z158,z8,z4,z5,z6]),(0,[z580,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z581,z8,z4,z5,z6]),(0,[z582,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z151,z5,z6,z55]),(0,[z2,z3,z8,z4,z583,z5,z6])],[(0,[z2,z3,z8,z584,z4,z5,z6]),(0,[z23,z3,z8,z4,z5,z6,z59]),(1,[z2,z3,z8,z232,z5,z6]),(0,[z2,z3,z8,z585,z4,z5,z6]),(0,[z586,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z6,z587]),(0,[z2,z3,z8,z5,z117,z6,z275])]],
   [[(0,[z1,z2,z3,z4,z21,z5,z6]),(0,[z2,z3,z8,z4,z108,z5,z6])],[(0,[z3,z8,z12,z4,z111,z5,z6]),(0,[z2,z3,z8,z4,z588,z5,z6]),(0,[z2,z3,z8,z96,z4,z151,z6]),(1,[z2,z3,z340,z4,z5,z6])],[(0,[z7,z2,z3,z8,z4,z66,z6]),(0,[z186,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z589,z4,z5,z6]),(0,[z590,z2,z3,z8,z4,z5,z6]),(0,[z591,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z222,z75,z5,z6]),(0,[z592,z2,z3,z8,z4,z5,z6])],[(0,[z186,z2,z3,z8,z4,z5,z59]),(0,[z2,z593,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z594,z5,z6]),(0,[z18,z2,z158,z8,z4,z5,z6]),(0,[z2,z3,z213,z8,z4,z5,z6]),(0,[z2,z3,z8,z595,z4,z5,z6])],[(0,[z2,z3,z8,z596,z4,z5,z6]),(0,[z13,z2,z3,z8,z4,z122,z6]),(0,[z2,z3,z8,z4,z5,z6,z597]),(0,[z2,z598,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z6,z599])],[(0,[z2,z3,z8,z600,z4,z5,z6]),(0,[z2,z158,z3,z8,z4,z80,z6]),(0,[z2,z3,z8,z4,z5,z205,z6]),(0,[z2,z273,z3,z8,z4,z5,z58]),(0,[z2,z3,z8,z4,z5,z601,z6])],[(0,[z2,z3,z8,z4,z602,z5,z6]),(0,[z2,z603,z3,z8,z4,z5,z6]),(0,[z57,z2,z273,z8,z4,z5,z6]),(0,[z604,z2,z3,z8,z4,z5,z6]),(0,[z13,z186,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z605,z6]),(0,[z2,z3,z8,z4,z5,z6,z606]),(0,[z607,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z54,z6])],[(0,[z2,z3,z8,z4,z5,z6,z608]),(0,[z2,z3,z8,z4,z5,z609,z6]),(0,[z2,z3,z8,z4,z610,z5,z6]),(0,[z87,z2,z3,z8,z4,z88,z6])]],
   [[(0,[z2,z3,z8,z4,z5,z6,z611]),(0,[z123,z2,z142,z8,z4,z5,z6]),(0,[z231,z2,z3,z156,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z42,z6])],[(0,[z102,z2,z3,z8,z4,z5,z6]),(0,[z3,z27,z8,z4,z5,z6,z59]),(0,[z612,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z613,z4,z5,z6]),(1,[z2,z258,z8,z4,z5,z6])],[(0,[z614,z2,z3,z8,z4,z5,z6]),(0,[z13,z2,z3,z536,z4,z5,z6]),(0,[z615,z2,z3,z8,z4,z5,z6]),(1,[z2,z3,z4,z5,z6,z183])],[(0,[z2,z3,z616,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z6,z617]),(0,[z2,z3,z8,z618,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z619,z6]),(0,[z2,z3,z8,z4,z5,z620,z6])],[(0,[z2,z3,z8,z4,z5,z6,z621]),(0,[z2,z8,z4,z19,z5,z188,z6]),(1,[z2,z3,z60,z222,z5,z6]),(0,[z2,z622,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z623,z4,z5,z6]),(0,[z2,z3,z8,z4,z624,z5,z6]),(0,[z56,z2,z3,z8,z4,z141,z6])],[(0,[z625,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z626,z6]),(1,[z2,z3,z8,z75,z5,z54])],[(0,[z627,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z628,z4,z5,z6]),(0,[z87,z2,z3,z213,z8,z4,z6])],[(0,[z2,z3,z15,z8,z4,z5,z6]),(0,[z629,z2,z3,z8,z4,z5,z6]),(0,[z77,z2,z3,z8,z4,z5,z55]),(0,[z630,z2,z3,z8,z4,z5,z6])]],
   [[(0,[z631,z2,z3,z8,z4,z5,z6]),(0,[z1,z2,z3,z72,z4,z5,z6]),(1,[z2,z3,z20,z4,z5,z42])],[(0,[z2,z3,z8,z632,z4,z5,z6]),(1,[z2,z3,z536,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z6,z633]),(0,[z2,z3,z8,z4,z5,z6,z634]),(0,[z635,z2,z3,z8,z4,z5,z6]),(1,[z2,z3,z8,z4,z432,z6])],[(0,[z175,z0,z2,z3,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z636,z6])],[(0,[z231,z102,z2,z8,z4,z5,z6]),(0,[z177,z2,z3,z4,z21,z5,z6]),(0,[z2,z3,z60,z4,z5,z6,z43])],[(0,[z2,z3,z8,z4,z5,z637,z6]),(0,[z638,z2,z3,z8,z4,z5,z6])],[(0,[z639,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z374,z5,z6]),(0,[z2,z3,z640,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z641,z6]),(0,[z2,z3,z8,z4,z5,z6,z642])],[(0,[z643,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z644,z8,z4,z5,z6]),(0,[z2,z3,z8,z645,z4,z5,z6]),(0,[z646,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z213,z8,z4,z61,z6])],[(0,[z2,z3,z8,z4,z647,z5,z6]),(0,[z2,z648,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z649,z6])]],
   [[(0,[z2,z3,z650,z8,z4,z5,z6]),(1,[z294,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z651,z4,z5,z6])],[(0,[z2,z3,z8,z216,z5,z80,z6]),(0,[z652,z2,z3,z8,z4,z5,z6]),(0,[z138,z2,z3,z8,z203,z5,z6]),(0,[z2,z3,z8,z4,z5,z6,z653]),(0,[z2,z654,z3,z8,z4,z5,z6])],[(0,[z2,z3,z8,z4,z5,z655,z6]),(0,[z123,z2,z8,z26,z4,z5,z6]),(0,[z656,z2,z3,z8,z4,z5,z6])],[(1,[z2,z3,z303,z4,z5,z6]),(0,[z657,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z658,z5,z6]),(0,[z0,z2,z3,z213,z4,z5,z6]),(0,[z659,z2,z3,z8,z4,z5,z6]),(1,[z300,z2,z3,z4,z5,z6]),(0,[z2,z3,z8,z4,z660,z5,z6]),(0,[z661,z2,z3,z8,z4,z5,z6])],[(0,[z662,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z663,z6]),(0,[z2,z3,z8,z4,z5,z361,z6]),(0,[z2,z3,z8,z4,z5,z6,z664]),(0,[z87,z2,z3,z8,z5,z88,z6]),(0,[z2,z3,z8,z4,z665,z5,z6]),(1,[z2,z3,z8,z4,z141,z117])],[(0,[z2,z3,z666,z8,z4,z5,z6]),(0,[z2,z3,z8,z667,z4,z5,z6]),(1,[z2,z3,z8,z4,z385,z6]),(0,[z2,z3,z8,z4,z5,z6,z668]),(0,[z2,z3,z8,z151,z5,z88,z6])],[(0,[z2,z3,z8,z4,z669,z5,z6]),(0,[z2,z3,z8,z4,z670,z5,z6])],[]],
   [[(0,[z2,z3,z8,z4,z5,z671,z6]),(0,[z2,z3,z8,z4,z5,z672,z6]),(0,[z2,z3,z8,z4,z5,z673,z6]),(0,[z2,z3,z309,z8,z4,z5,z6])],[(0,[z2,z3,z8,z4,z5,z674,z6]),(0,[z2,z3,z8,z4,z675,z5,z6]),(0,[z2,z676,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z76,z5,z6,z55])],[(0,[z2,z3,z8,z4,z5,z677,z6]),(0,[z2,z3,z8,z4,z5,z678,z6]),(0,[z2,z3,z679,z8,z4,z5,z6]),(0,[z2,z8,z115,z4,z132,z5,z6]),(0,[z2,z3,z8,z4,z680,z5,z6])],[(1,[z102,z27,z8,z4,z5,z6]),(0,[z13,z2,z3,z8,z4,z5,z59]),(0,[z681,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z682,z6]),(0,[z2,z3,z8,z4,z683,z5,z6])],[(0,[z2,z3,z8,z4,z5,z6,z684]),(1,[z2,z3,z8,z96,z151,z6])],[(0,[z685,z2,z3,z8,z4,z5,z6]),(0,[z129,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z686,z8,z4,z5,z6]),(0,[z687,z2,z3,z8,z4,z5,z6])],[(0,[z175,z3,z8,z72,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z688,z6]),(0,[z2,z3,z8,z4,z689,z5,z6])],[(0,[z690,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z432,z76,z6]),(1,[z2,z3,z213,z4,z21,z6]),(0,[z2,z3,z8,z4,z5,z6,z691])]],
   [[(0,[z2,z3,z8,z4,z5,z692,z6])],[(1,[z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z358,z6]),(0,[z693,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z694,z5,z6]),(0,[z0,z2,z3,z4,z5,z61,z6]),(0,[z695,z2,z3,z8,z4,z5,z6])],[(0,[z2,z27,z8,z4,z19,z5,z6]),(0,[z2,z3,z140,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z696,z6]),(0,[z107,z2,z3,z4,z5,z80,z6]),(0,[z13,z2,z3,z15,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z697,z6])],[(0,[z2,z3,z8,z4,z5,z698,z6]),(0,[z186,z3,z8,z4,z5,z274,z6]),(0,[z699,z2,z3,z8,z4,z5,z6])],[(0,[z18,z2,z3,z8,z4,z66,z6]),(0,[z2,z3,z8,z115,z4,z5,z6]),(0,[z2,z3,z8,z4,z700,z5,z6]),(0,[z2,z3,z8,z4,z5,z6,z701])],[(0,[z2,z3,z8,z4,z5,z6,z702]),(0,[z2,z3,z309,z4,z5,z117,z6])],[(0,[z175,z2,z3,z4,z21,z5,z6]),(0,[z703,z2,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z704,z5,z6]),(1,[z2,z3,z8,z127,z5,z6])],[(0,[z2,z3,z8,z4,z5,z705,z6]),(0,[z706,z2,z3,z8,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z2,z158,z8,z4,z178,z6]),(0,[z2,z707,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z708,z6]),(0,[z2,z3,z4,z5,z709,z6]),(0,[z2,z3,z8,z710,z5,z6]),(0,[z2,z258,z8,z4,z5,z6]),(0,[z2,z8,z4,z5,z6,z711])],[(0,[z2,z712,z8,z4,z5,z6]),(0,[z13,z14,z8,z4,z5,z59]),(0,[z22,z2,z8,z115,z5,z6]),(0,[z2,z273,z8,z4,z5,z713]),(0,[z406,z2,z3,z4,z6,z43]),(0,[z2,z3,z4,z5,z6,z183]),(0,[z2,z3,z714,z4,z5,z6])],[(0,[z23,z129,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z122,z6]),(0,[z2,z3,z715,z4,z5,z6]),(0,[z2,z3,z716,z4,z5,z6]),(0,[z717,z2,z3,z4,z5,z6])],[(0,[z2,z718,z8,z4,z5,z6]),(0,[z2,z3,z719,z4,z5,z6]),(0,[z294,z3,z8,z4,z385,z6]),(0,[z2,z3,z60,z222,z5,z6]),(0,[z720,z3,z8,z4,z5,z6]),(0,[z2,z721,z8,z4,z5,z6]),(0,[z2,z3,z309,z4,z5,z6])]],
   [[(0,[z2,z27,z8,z4,z24,z6]),(0,[z2,z3,z722,z4,z5,z6]),(0,[z2,z3,z8,z4,z723,z6]),(0,[z537,z3,z8,z4,z80,z6]),(0,[z2,z724,z8,z4,z5,z6]),(0,[z725,z2,z3,z8,z5,z6]),(0,[z726,z3,z8,z4,z5,z6]),(0,[z2,z3,z156,z4,z385,z6]),(0,[z2,z727,z8,z4,z5,z6])],[(0,[z2,z3,z8,z4,z108,z6]),(0,[z184,z3,z156,z4,z5,z6]),(0,[z2,z728,z8,z4,z5,z6])],[(0,[z2,z158,z8,z4,z677,z6]),(0,[z2,z3,z729,z4,z5,z6]),(0,[z2,z3,z303,z4,z385,z6])],[(0,[z23,z454,z8,z4,z5,z6]),(0,[z1,z3,z4,z5,z472,z6]),(0,[z730,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z731,z5,z6]),(0,[z2,z3,z732,z4,z5,z6]),(0,[z184,z3,z303,z4,z5,z6]),(0,[z2,z3,z20,z4,z5,z42]),(0,[z56,z2,z3,z8,z4,z733])]],
   [[(0,[z734,z3,z8,z4,z5,z6]),(0,[z2,z3,z536,z4,z5,z6]),(0,[z2,z3,z735,z4,z5,z6]),(0,[z231,z294,z8,z4,z5,z58]),(0,[z0,z287,z2,z3,z5,z6]),(1,[z2,z3,z8,z5,z736]),(0,[z2,z3,z134,z5,z6,z183])],[(0,[z734,z102,z8,z4,z5,z6]),(0,[z129,z27,z8,z4,z5,z6]),(0,[z2,z3,z8,z737,z5,z6]),(0,[z551,z2,z3,z8,z4,z118]),(0,[z2,z3,z8,z4,z149,z6]),(0,[z2,z3,z4,z5,z6,z738]),(0,[z87,z2,z3,z271,z8,z6]),(0,[z2,z3,z222,z5,z189,z6]),(0,[z2,z3,z8,z4,z739,z6]),(0,[z56,z2,z8,z4,z174,z118]),(0,[z2,z3,z8,z4,z141,z733])],[(0,[z2,z3,z8,z740,z5,z6]),(0,[z2,z3,z8,z741,z5,z6]),(0,[z2,z8,z4,z5,z6,z742]),(0,[z300,z87,z2,z3,z5,z6])],[(0,[z2,z3,z8,z743,z5,z6]),(0,[z2,z3,z744,z4,z5,z6]),(0,[z2,z8,z4,z5,z6,z745]),(0,[z2,z3,z4,z5,z746,z6])]],
   [[(0,[z2,z3,z747,z4,z5,z6]),(0,[z177,z406,z2,z3,z8,z6])],[(0,[z2,z3,z4,z5,z6,z748]),(0,[z2,z3,z8,z749,z5,z6]),(0,[z750,z3,z8,z4,z5,z6])],[(0,[z2,z3,z8,z4,z751,z6]),(0,[z2,z3,z8,z752,z5,z6]),(0,[z2,z3,z753,z4,z5,z6]),(0,[z186,z29,z8,z4,z5,z6]),(0,[z405,z2,z3,z8,z5,z55]),(0,[z754,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z713]),(0,[z2,z3,z8,z4,z6,z755]),(0,[z2,z3,z4,z21,z739,z6]),(0,[z2,z3,z78,z75,z5,z6])],[(0,[z2,z3,z8,z5,z756,z6]),(0,[z7,z3,z8,z4,z66,z6]),(0,[z2,z258,z8,z4,z66,z6]),(0,[z13,z129,z8,z4,z5,z59]),(0,[z2,z3,z8,z4,z757,z6]),(0,[z2,z3,z8,z203,z5,z6]),(0,[z2,z758,z8,z4,z5,z6]),(1,[z2,z3,z8,z759,z6]),(0,[z56,z2,z258,z8,z4,z118])]],
   [[(0,[z2,z760,z8,z4,z5,z6]),(0,[z120,z2,z3,z8,z5,z6]),(0,[z2,z3,z761,z4,z5,z6]),(0,[z2,z158,z8,z4,z549,z6]),(0,[z2,z3,z536,z374,z5,z6]),(0,[z2,z3,z762,z4,z5,z6])],[(0,[z2,z3,z8,z763,z5,z6]),(0,[z1,z3,z140,z4,z5,z6]),(1,[z3,z764,z4,z5,z6]),(1,[z3,z8,z4,z5,z765]),(0,[z2,z3,z8,z4,z5,z765]),(0,[z2,z3,z8,z766,z5,z6]),(0,[z2,z3,z767,z4,z5,z6]),(0,[z2,z3,z213,z4,z660,z6])],[(0,[z175,z3,z72,z4,z5,z6]),(0,[z768,z2,z3,z8,z5,z6]),(0,[z769,z2,z8,z4,z5,z6]),(0,[z2,z29,z536,z4,z5,z6]),(0,[z2,z3,z4,z739,z61,z6]),(0,[z2,z3,z8,z4,z6,z733])],[(0,[z2,z3,z8,z770,z5,z6]),(0,[z107,z2,z3,z216,z5,z6]),(0,[z406,z2,z3,z20,z4,z6]),(0,[z2,z3,z8,z4,z141,z117])]],
   [[(0,[z2,z3,z771,z4,z5,z6]),(0,[z65,z3,z4,z63,z80,z6]),(0,[z2,z3,z8,z4,z385,z6]),(0,[z2,z258,z8,z4,z19,z6]),(0,[z772,z2,z3,z8,z4,z6]),(0,[z2,z8,z773,z4,z5,z6]),(0,[z87,z2,z3,z8,z97,z6]),(0,[z2,z3,z8,z75,z5,z736])],[(0,[z184,z3,z8,z4,z5,z6]),(0,[z3,z764,z72,z4,z5,z6]),(0,[z2,z3,z8,z75,z5,z484]),(0,[z774,z2,z3,z4,z5,z6]),(0,[z775,z3,z8,z4,z5,z6]),(0,[z231,z2,z8,z4,z5,z48]),(0,[z2,z158,z8,z4,z163,z6]),(0,[z2,z3,z8,z776,z5,z6]),(0,[z777,z3,z8,z4,z5,z6]),(0,[z778,z3,z8,z4,z5,z6])],[(0,[z23,z57,z8,z4,z5,z6]),(0,[z2,z3,z779,z4,z5,z6]),(0,[z2,z3,z8,z780,z5,z6]),(0,[z2,z781,z8,z4,z5,z6]),(0,[z782,z3,z8,z4,z5,z6])],[(0,[z2,z3,z8,z4,z783,z6]),(0,[z32,z3,z140,z4,z5,z6]),(0,[z3,z8,z4,z66,z784,z6]),(0,[z2,z14,z536,z4,z5,z6]),(0,[z13,z3,z8,z4,z122,z59]),(0,[z2,z3,z8,z785,z5,z6]),(0,[z428,z2,z8,z132,z5,z6]),(0,[z2,z3,z4,z5,z6,z786]),(0,[z2,z3,z8,z5,z6,z787]),(0,[z2,z3,z4,z5,z788,z43])]],
   [[(0,[z231,z2,z8,z4,z149,z58]),(0,[z789,z2,z3,z8,z5,z6])],[(0,[z790,z2,z3,z8,z5,z6]),(0,[z2,z3,z8,z4,z791,z6]),(0,[z2,z3,z792,z4,z5,z6]),(0,[z231,z2,z156,z4,z5,z58]),(0,[z2,z3,z8,z4,z6,z793])],[(0,[z102,z27,z8,z4,z5,z6]),(0,[z2,z3,z794,z4,z5,z6]),(0,[z13,z3,z8,z4,z108,z59]),(0,[z2,z3,z4,z5,z6,z795])],[(0,[z2,z3,z796,z4,z5,z6]),(0,[z0,z287,z2,z3,z61,z6]),(0,[z0,z2,z3,z361,z61,z6])]],
   [[(0,[z2,z3,z8,z4,z797,z6]),(0,[z3,z8,z4,z5,z6,z798]),(0,[z799,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z172,z149,z6])],[(0,[z2,z3,z8,z4,z800,z6]),(0,[z2,z3,z8,z801,z5,z6]),(0,[z2,z3,z8,z216,z5,z6]),(0,[z11,z3,z8,z802,z5,z6]),(0,[z803,z2,z3,z8,z5,z6]),(0,[z2,z3,z804,z4,z5,z6]),(0,[z13,z3,z536,z4,z5,z59]),(0,[z2,z805,z8,z4,z5,z6]),(0,[z2,z3,z8,z141,z117,z275])],[(0,[z2,z3,z8,z4,z6,z806]),(0,[z177,z2,z3,z432,z76,z6]),(0,[z2,z3,z213,z4,z21,z6]),(0,[z2,z3,z8,z4,z5,z788]),(0,[z2,z3,z8,z5,z54,z736])],[(0,[z2,z3,z8,z4,z6,z807]),(0,[z2,z3,z8,z808,z5,z6]),(0,[z2,z3,z78,z4,z5,z6]),(0,[z2,z3,z20,z4,z5,z439]),(0,[z2,z3,z8,z75,z5,z221]),(0,[z77,z2,z3,z78,z5,z55])]],
   [[(0,[z2,z809,z8,z4,z5,z6]),(0,[z2,z3,z216,z5,z63,z6]),(0,[z2,z3,z8,z810,z5,z6]),(0,[z2,z3,z8,z4,z811,z6]),(0,[z2,z3,z4,z21,z6,z347])],[(0,[z2,z8,z4,z5,z6,z812]),(0,[z2,z8,z4,z5,z6,z713]),(0,[z2,z813,z8,z4,z5,z6])],[(0,[z2,z3,z8,z4,z814,z6]),(0,[z194,z2,z3,z8,z4,z118]),(0,[z2,z815,z8,z4,z5,z6]),(0,[z294,z3,z8,z232,z5,z6]),(0,[z2,z3,z8,z96,z759,z6])],[(0,[z2,z8,z4,z5,z205,z359]),(0,[z2,z3,z816,z4,z5,z6]),(0,[z2,z3,z156,z232,z5,z6]),(1,[z177,z406,z2,z3,z6]),(0,[z2,z817,z8,z4,z5,z6])]],
   [[(0,[z2,z3,z8,z818,z5,z6]),(0,[z2,z3,z8,z4,z819,z6]),(0,[z3,z140,z764,z4,z5,z6]),(0,[z2,z820,z8,z4,z5,z6]),(0,[z2,z821,z3,z8,z4,z6]),(0,[z2,z3,z822,z4,z5,z6]),(0,[z253,z2,z8,z4,z19,z6])],[(0,[z13,z3,z8,z4,z5,z765]),(0,[z2,z3,z303,z232,z5,z6]),(0,[z87,z2,z3,z8,z233,z6]),(1,[z0,z287,z2,z3,z6]),(0,[z2,z3,z8,z4,z5,z736])],[(0,[z2,z823,z8,z4,z5,z6]),(0,[z13,z8,z4,z5,z67,z59]),(0,[z129,z294,z8,z4,z5,z6]),(0,[z2,z3,z8,z824,z5,z6]),(0,[z2,z3,z776,z76,z5,z6])],[(0,[z2,z3,z8,z4,z358,z6]),(0,[z825,z2,z8,z4,z5,z6]),(0,[z175,z471,z3,z4,z5,z6]),(0,[z2,z3,z8,z5,z6,z826]),(0,[z2,z3,z8,z4,z827,z6]),(0,[z2,z3,z8,z172,z385,z6])]],
   [[(0,[z488,z2,z8,z4,z19,z6]),(0,[z2,z3,z8,z4,z828,z6]),(0,[z2,z3,z15,z4,z5,z6]),(0,[z443,z3,z72,z4,z5,z6]),(0,[z2,z3,z8,z374,z5,z6]),(0,[z2,z8,z4,z829,z5,z6]),(0,[z184,z3,z8,z172,z5,z6]),(0,[z2,z3,z8,z4,z830,z6]),(0,[z2,z3,z8,z75,z5,z150]),(0,[z2,z3,z8,z831,z5,z6])],[(1,[z3,z8,z4,z784,z6]),(0,[z2,z3,z8,z4,z784,z6]),(0,[z2,z3,z4,z5,z6,z832])],[(0,[z2,z29,z8,z4,z5,z6]),(0,[z11,z3,z8,z230,z5,z6]),(0,[z3,z8,z4,z5,z6,z833])],[(0,[z834,z2,z3,z8,z4,z5]),(0,[z2,z3,z8,z4,z835,z6]),(0,[z2,z3,z4,z5,z836,z6]),(0,[z2,z3,z8,z837,z5,z6]),(0,[z7,z91,z8,z4,z66,z6]),(0,[z838,z2,z3,z8,z5,z6]),(0,[z114,z2,z8,z810,z5,z6]),(1,[z2,z3,z4,z739,z6]),(0,[z0,z287,z2,z3,z8,z6]),(0,[z2,z3,z4,z5,z6,z839])]],
   [[(0,[z2,z3,z8,z840,z5,z6]),(0,[z456,z57,z8,z4,z5,z6]),(0,[z2,z273,z8,z4,z5,z205]),(0,[z2,z258,z8,z4,z149,z6]),(0,[z2,z8,z4,z5,z205,z713]),(0,[z177,z406,z2,z3,z5,z6]),(0,[z2,z3,z4,z5,z739,z6])],[(0,[z2,z3,z8,z841,z5,z6]),(0,[z2,z3,z8,z4,z842,z6]),(0,[z2,z843,z8,z4,z5,z6]),(0,[z2,z8,z4,z5,z6,z844]),(0,[z2,z3,z536,z4,z122,z6]),(0,[z2,z3,z8,z4,z845,z6]),(0,[z138,z2,z3,z127,z5,z43])],[(0,[z2,z3,z8,z4,z846,z6]),(0,[z661,z3,z8,z4,z80,z6]),(0,[z2,z3,z8,z847,z5,z6]),(0,[z848,z2,z3,z4,z5,z6])],[(0,[z2,z14,z8,z4,z5,z6]),(0,[z27,z8,z4,z5,z6,z325]),(0,[z64,z27,z8,z4,z5,z6]),(0,[z65,z3,z8,z216,z80,z6]),(0,[z2,z3,z8,z4,z6,z849]),(0,[z2,z3,z8,z5,z361,z6]),(0,[z2,z3,z222,z776,z5,z6])]],
   [[(0,[z2,z3,z8,z4,z141,z356]),(0,[z2,z3,z536,z4,z108,z6]),(0,[z2,z3,z15,z374,z5,z6]),(0,[z2,z3,z8,z4,z850,z6]),(0,[z851,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z134,z5,z6])],[(0,[z2,z3,z8,z4,z5,z852]),(0,[z2,z3,z8,z853,z5,z6]),(0,[z2,z3,z8,z4,z854,z6]),(0,[z855,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z5,z6,z275]),(0,[z2,z3,z8,z151,z6,z224])],[(0,[z2,z29,z15,z4,z5,z6]),(0,[z2,z29,z8,z374,z5,z6]),(0,[z3,z8,z4,z856,z5,z6])],[(0,[z231,z2,z8,z4,z5,z325]),(0,[z2,z3,z8,z4,z857,z6]),(0,[z2,z3,z8,z858,z5,z6]),(0,[z2,z3,z8,z232,z5,z6]),(0,[z2,z3,z8,z4,z859,z6]),(1,[z300,z87,z2,z3,z6]),(0,[z300,z2,z3,z96,z4,z6])]],
   [[(0,[z2,z3,z8,z860,z5,z6]),(0,[z861,z2,z3,z8,z5,z6]),(0,[z2,z3,z8,z862,z5,z6]),(0,[z2,z863,z8,z4,z5,z6]),(1,[z2,z864,z4,z5,z6]),(0,[z294,z8,z4,z5,z6,z58])],[(0,[z2,z8,z4,z5,z6,z865]),(0,[z866,z2,z3,z4,z5,z6]),(0,[z2,z3,z8,z867,z5,z6]),(0,[z87,z2,z3,z8,z696,z6])],[(0,[z3,z8,z764,z4,z5,z6]),(0,[z2,z868,z8,z4,z5,z6]),(0,[z2,z91,z8,z4,z80,z6]),(0,[z2,z3,z536,z483,z5,z6]),(0,[z2,z8,z4,z5,z6,z869]),(0,[z2,z3,z8,z4,z870,z6]),(0,[z871,z3,z8,z4,z5,z6]),(0,[z2,z158,z8,z4,z188,z6]),(0,[z287,z2,z3,z8,z5,z6]),(0,[z2,z3,z8,z96,z451,z6])],[(0,[z2,z3,z8,z4,z24,z6]),(0,[z102,z294,z8,z4,z5,z6]),(0,[z2,z14,z15,z4,z5,z6]),(0,[z2,z14,z8,z374,z5,z6]),(0,[z3,z8,z4,z5,z6,z765]),(0,[z3,z8,z4,z5,z6,z872]),(0,[z2,z3,z20,z127,z5,z6]),(0,[z2,z3,z8,z151,z759,z6]),(0,[z2,z3,z873,z4,z5,z6]),(0,[z2,z3,z8,z5,z736,z55])]],
   [[(0,[z2,z3,z20,z4,z5,z368]),(0,[z7,z136,z8,z4,z66,z6]),(0,[z3,z8,z4,z5,z765,z59]),(0,[z2,z8,z4,z19,z6,z469])],[(0,[z2,z3,z8,z874,z5,z6]),(0,[z2,z3,z8,z875,z5,z6]),(0,[z2,z876,z8,z4,z5,z6])],[(0,[z2,z877,z8,z4,z5,z6]),(0,[z2,z3,z878,z4,z5,z6]),(0,[z3,z8,z4,z5,z274,z765]),(0,[z2,z8,z4,z5,z713,z58]),(0,[z879,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z5,z6,z880])],[(0,[z2,z3,z8,z881,z5,z6]),(0,[z2,z3,z882,z4,z5,z6]),(0,[z2,z8,z864,z4,z5,z6]),(0,[z2,z8,z4,z883,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z332,z6]),(0,[z2,z3,z4,z5,z6,z884]),(0,[z2,z3,z8,z885,z5,z6]),(0,[z2,z3,z20,z4,z5,z682]),(0,[z2,z3,z886,z4,z5,z6]),(0,[z294,z8,z4,z19,z5,z6]),(0,[z2,z8,z4,z19,z149,z6]),(0,[z294,z3,z156,z4,z5,z6]),(0,[z231,z2,z8,z172,z5,z58]),(0,[z177,z2,z3,z776,z5,z6]),(0,[z2,z887,z8,z4,z5,z6])],[(0,[z13,z3,z8,z374,z5,z59]),(0,[z888,z3,z8,z4,z5,z6]),(0,[z87,z2,z3,z145,z88,z6])],[(0,[z2,z3,z889,z4,z5,z6]),(0,[z279,z2,z3,z4,z5,z43]),(0,[z2,z8,z4,z5,z890,z6]),(0,[z2,z3,z891,z4,z5,z6]),(0,[z294,z3,z303,z4,z5,z6]),(0,[z892,z3,z8,z4,z5,z6])],[(0,[z2,z3,z893,z4,z5,z6]),(0,[z2,z8,z4,z827,z5,z6]),(0,[z294,z273,z8,z4,z5,z6]),(0,[z87,z2,z3,z8,z759,z6])]],
   [[(0,[z574,z2,z8,z4,z5,z58]),(0,[z107,z65,z3,z4,z80,z6]),(0,[z2,z3,z894,z4,z5,z6]),(0,[z2,z3,z895,z4,z5,z6]),(0,[z896,z3,z8,z4,z5,z6]),(1,[z2,z3,z4,z5,z788]),(0,[z138,z2,z3,z4,z5,z788]),(0,[z2,z3,z8,z5,z348,z55])],[(0,[z160,z3,z8,z802,z5,z6]),(0,[z2,z897,z3,z8,z4,z6]),(0,[z3,z8,z4,z784,z80,z6]),(0,[z2,z898,z8,z4,z5,z6]),(0,[z899,z2,z8,z4,z5,z6]),(0,[z2,z3,z8,z900,z5,z6]),(0,[z901,z3,z8,z4,z5,z6]),(0,[z184,z3,z8,z4,z149,z6]),(0,[z2,z3,z8,z5,z6,z902]),(0,[z2,z3,z8,z5,z759,z6]),(0,[z2,z3,z8,z75,z5,z54])],[(0,[z2,z3,z903,z4,z5,z6]),(0,[z107,z120,z2,z3,z5,z6]),(0,[z2,z3,z8,z904,z5,z6]),(0,[z2,z3,z8,z5,z6,z905]),(0,[z231,z2,z8,z232,z5,z58]),(0,[z2,z906,z8,z4,z5,z6])],[(0,[z2,z3,z907,z4,z5,z6]),(0,[z2,z908,z8,z4,z5,z6]),(0,[z2,z3,z909,z4,z5,z6]),(0,[z2,z910,z3,z8,z4,z6])]],
   [[(0,[z2,z911,z8,z4,z5,z6]),(0,[z120,z2,z3,z5,z63,z6]),(0,[z2,z8,z4,z5,z6,z174]),(0,[z0,z2,z3,z441,z4,z6]),(0,[z2,z3,z8,z912,z5,z6]),(0,[z2,z3,z4,z5,z6,z913])],[(0,[z393,z2,z26,z4,z5,z6]),(0,[z2,z3,z8,z4,z914,z6]),(0,[z406,z2,z3,z222,z4,z6]),(0,[z2,z3,z8,z4,z432,z6])],[(0,[z2,z3,z8,z4,z915,z6]),(0,[z916,z2,z8,z4,z5,z6]),(0,[z2,z917,z8,z4,z5,z6]),(0,[z615,z2,z3,z4,z5,z43]),(0,[z2,z8,z4,z810,z5,z6]),(0,[z918,z3,z8,z4,z5,z6])],[(0,[z129,z2,z8,z4,z5,z6]),(0,[z919,z2,z3,z4,z5,z6]),(0,[z3,z8,z4,z784,z5,z6]),(0,[z920,z2,z3,z4,z5,z6])]],
   [[(0,[z2,z3,z8,z4,z921,z6]),(0,[z2,z922,z8,z4,z5,z6]),(0,[z923,z2,z8,z4,z5,z6]),(0,[z924,z3,z8,z4,z5,z6]),(0,[z925,z3,z8,z4,z5,z6]),(0,[z231,z2,z8,z4,z5,z713]),(1,[z2,z3,z8,z4,z733])],[(0,[z2,z136,z8,z4,z5,z6]),(0,[z2,z3,z8,z926,z5,z6]),(0,[z18,z2,z8,z4,z827,z6]),(0,[z2,z3,z8,z927,z5,z6])],[(0,[z2,z3,z8,z928,z5,z6]),(0,[z2,z3,z8,z4,z5,z929]),(0,[z2,z158,z8,z4,z827,z6])],[(0,[z2,z3,z930,z4,z5,z6]),(0,[z2,z3,z8,z4,z931,z6]),(0,[z2,z91,z8,z4,z66,z6]),(0,[z87,z2,z3,z8,z578,z6]),(0,[z2,z3,z4,z5,z145,z6]),(0,[z77,z2,z3,z340,z5,z55])]],
   [[(0,[z294,z3,z8,z4,z5,z6]),(0,[z3,z8,z802,z111,z5,z6]),(0,[z7,z3,z8,z4,z784,z6]),(0,[z2,z3,z8,z932,z5,z6]),(0,[z184,z3,z8,z4,z385,z6]),(0,[z304,z2,z3,z76,z5,z6])],[(0,[z2,z933,z8,z4,z5,z6]),(0,[z934,z2,z3,z4,z5,z6]),(0,[z935,z2,z8,z4,z5,z6]),(0,[z456,z3,z8,z4,z66,z6]),(0,[z2,z3,z15,z4,z122,z6]),(0,[z2,z3,z8,z374,z122,z6]),(0,[z2,z3,z156,z4,z5,z6]),(0,[z2,z3,z127,z5,z6,z43]),(0,[z936,z2,z3,z4,z5,z6])],[(0,[z2,z3,z764,z4,z5,z6]),(0,[z2,z8,z937,z4,z5,z6]),(0,[z2,z3,z8,z483,z5,z6]),(0,[z2,z938,z3,z8,z4,z6]),(0,[z2,z3,z8,z4,z141,z492]),(0,[z2,z939,z8,z4,z5,z6]),(0,[z2,z3,z8,z940,z5,z6])],[(0,[z23,z294,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z941,z6]),(0,[z2,z3,z8,z942,z5,z6]),(0,[z2,z29,z8,z4,z122,z6]),(0,[z2,z3,z303,z4,z5,z6]),(0,[z2,z3,z8,z943,z5,z6]),(0,[z300,z2,z3,z4,z5,z6]),(0,[z177,z2,z3,z312,z5,z6]),(0,[z944,z2,z8,z4,z5,z6])]],
   [[(0,[z2,z3,z8,z4,z945,z6]),(0,[z2,z3,z15,z4,z108,z6]),(0,[z2,z3,z8,z374,z108,z6]),(0,[z946,z3,z8,z4,z5,z6])],[(0,[z494,z2,z3,z8,z5,z55]),(0,[z2,z3,z60,z262,z5,z6]),(0,[z2,z3,z4,z21,z124,z6]),(0,[z77,z2,z3,z8,z5,z736])],[(0,[z336,z27,z8,z4,z5,z6]),(0,[z947,z2,z8,z4,z5,z6]),(0,[z2,z29,z8,z4,z108,z6]),(0,[z2,z3,z8,z4,z948,z6]),(0,[z2,z3,z8,z4,z5,z949]),(0,[z950,z3,z8,z4,z5,z6]),(0,[z2,z3,z5,z6,z183,z275])],[(0,[z2,z3,z8,z4,z951,z6]),(0,[z107,z2,z3,z4,z5,z6]),(0,[z952,z3,z8,z4,z5,z6])]],
   [[(0,[z2,z14,z8,z4,z122,z6]),(0,[z2,z3,z8,z5,z953,z6]),(0,[z529,z2,z3,z76,z5,z6]),(0,[z2,z3,z4,z5,z101,z43]),(0,[z2,z954,z8,z4,z5,z6]),(0,[z2,z3,z955,z4,z5,z6]),(0,[z300,z87,z2,z3,z88,z6])],[(0,[z2,z3,z8,z956,z5,z6]),(0,[z734,z27,z8,z4,z5,z6]),(0,[z957,z2,z3,z4,z5,z6]),(0,[z2,z3,z8,z4,z958,z6]),(0,[z2,z3,z8,z5,z6,z736])],[(0,[z734,z2,z8,z4,z5,z6]),(0,[z2,z3,z8,z959,z5,z6]),(0,[z2,z3,z8,z960,z5,z6]),(0,[z2,z3,z15,z483,z5,z6]),(0,[z18,z2,z8,z4,z19,z6]),(0,[z2,z3,z8,z5,z6,z961]),(0,[z177,z406,z2,z3,z76,z6]),(0,[z2,z3,z309,z134,z5,z6])],[(0,[z2,z3,z8,z5,z6,z962]),(0,[z2,z14,z8,z4,z108,z6]),(0,[z2,z3,z8,z4,z963,z6]),(0,[z177,z406,z2,z3,z4,z6]),(0,[z3,z8,z4,z5,z6,z964]),(0,[z2,z3,z309,z5,z6,z275])]],
   [[(0,[z29,z8,z4,z5,z6,z59]),(0,[z2,z29,z8,z483,z5,z6]),(0,[z2,z3,z8,z96,z151,z6]),(0,[z2,z965,z8,z4,z5,z6])],[(0,[z2,z3,z8,z966,z5,z6]),(0,[z0,z2,z3,z4,z61,z6])],[(0,[z2,z3,z8,z151,z637,z6]),(0,[z2,z3,z967,z4,z5,z6]),(0,[z2,z8,z4,z19,z827,z6]),(0,[z2,z3,z8,z4,z5,z968]),(0,[z138,z2,z3,z203,z5,z43]),(0,[z300,z2,z3,z151,z5,z6])],[(1,[z734,z8,z4,z5,z6]),(0,[z2,z969,z8,z4,z5,z6])]],
   [[(0,[z2,z970,z8,z4,z5,z6]),(0,[z971,z2,z3,z8,z5,z6]),(0,[z972,z3,z8,z4,z5,z6]),(1,[z2,z8,z4,z5,z713]),(0,[z2,z3,z4,z5,z6,z788]),(0,[z77,z2,z3,z8,z5,z55])],[(0,[z2,z3,z8,z4,z5,z6]),(0,[z57,z2,z8,z4,z24,z6]),(0,[z2,z973,z3,z8,z4,z6]),(0,[z18,z2,z8,z4,z567,z6]),(0,[z2,z14,z8,z483,z5,z6]),(0,[z974,z3,z8,z4,z5,z6]),(0,[z975,z3,z8,z4,z5,z6]),(0,[z2,z3,z8,z151,z649,z6])],[(0,[z2,z3,z976,z4,z5,z6]),(0,[z2,z3,z977,z4,z5,z6]),(0,[z100,z57,z8,z4,z5,z6]),(0,[z2,z3,z8,z4,z6,z978]),(0,[z2,z3,z8,z979,z5,z6]),(0,[z231,z2,z303,z4,z5,z58]),(0,[z2,z3,z60,z776,z5,z6])],[(0,[z2,z3,z980,z4,z5,z6]),(0,[z294,z3,z8,z172,z5,z6]),(0,[z2,z3,z8,z232,z149,z6]),(0,[z177,z2,z3,z76,z5,z6]),(0,[z0,z2,z3,z4,z435,z6]),(0,[z2,z3,z981,z4,z5,z6]),(0,[z2,z3,z78,z5,z6,z55])]],
   [[(0,[z2,z3,z8,z4,z982,z6]),(0,[z23,z57,z8,z4,z358,z6]),(0,[z2,z3,z4,z5,z63,z6]),(0,[z160,z3,z330,z8,z5,z6]),(0,[z983,z2,z3,z4,z5,z6]),(0,[z984,z3,z8,z4,z5,z6]),(0,[z2,z3,z156,z172,z5,z6]),(0,[z231,z2,z8,z4,z385,z58]),(0,[z577,z2,z3,z76,z5,z6])],[(0,[z574,z3,z8,z4,z5,z59]),(0,[z2,z3,z8,z4,z985,z6]),(0,[z2,z3,z986,z4,z5,z6]),(0,[z160,z3,z8,z111,z5,z6]),(0,[z2,z3,z8,z4,z5,z987]),(0,[z988,z3,z8,z4,z5,z6]),(0,[z2,z3,z4,z5,z989,z6]),(0,[z2,z3,z8,z4,z117,z733])],[(0,[z2,z3,z8,z990,z5,z6]),(0,[z2,z3,z991,z4,z5,z6]),(0,[z2,z3,z8,z4,z992,z6]),(0,[z2,z3,z303,z172,z5,z6]),(0,[z2,z3,z8,z127,z5,z6])],[(0,[z23,z734,z8,z4,z5,z6]),(0,[z2,z993,z8,z4,z5,z6]),(0,[z13,z3,z8,z483,z5,z59]),(0,[z2,z142,z864,z4,z5,z6]),(0,[z2,z3,z8,z994,z5,z6]),(0,[z2,z3,z995,z4,z5,z6]),(0,[z56,z2,z3,z8,z4,z118]),(0,[z2,z3,z8,z4,z733,z118])]],
   [[(0,[z0,z2,z3,z4,z578,z6])],[(0,[z23,z8,z4,z5,z6,z684]),(0,[z114,z2,z8,z132,z5,z6]),(0,[z2,z8,z115,z810,z5,z6]),(0,[z177,z2,z3,z233,z5,z6]),(0,[z2,z3,z8,z759,z88,z6])],[(0,[z2,z996,z8,z4,z5,z6]),(0,[z2,z3,z4,z21,z364,z6]),(0,[z2,z3,z8,z4,z997,z6]),(0,[z516,z2,z3,z8,z5,z55]),(0,[z2,z3,z864,z4,z5,z6]),(0,[z2,z8,z810,z132,z5,z6]),(0,[z2,z3,z4,z776,z5,z6]),(0,[z406,z2,z3,z8,z4,z6]),(0,[z406,z2,z3,z8,z6,z55]),(0,[z2,z3,z8,z134,z141,z117])],[(0,[z11,z3,z8,z12,z5,z6]),(0,[z998,z3,z8,z4,z5,z6])]],
   [[(0,[z2,z3,z8,z4,z999,z6]),(0,[z2,z1000,z8,z4,z5,z6]),(0,[z2,z3,z1001,z4,z5,z6]),(0,[z2,z1002,z8,z4,z5,z6]),(0,[z2,z3,z464,z222,z5,z6])],[(0,[z2,z3,z8,z4,z1003,z6]),(0,[z1,z3,z764,z4,z5,z6]),(0,[z3,z8,z4,z802,z5,z6]),(0,[z2,z3,z4,z5,z6,z1004]),(0,[z2,z3,z1005,z4,z5,z6]),(0,[z1006,z2,z3,z8,z5,z6])],[(0,[z2,z3,z8,z4,z1007,z6]),(0,[z123,z2,z26,z4,z5,z6]),(0,[z2,z3,z8,z232,z385,z6]),(0,[z2,z3,z4,z5,z42,z788]),(0,[z300,z87,z2,z3,z8,z6]),(0,[z3,z8,z4,z5,z6,z1008])],[(0,[z2,z3,z8,z4,z1009,z6]),(0,[z2,z3,z8,z4,z1010,z6]),(0,[z630,z3,z8,z111,z5,z6]),(0,[z3,z8,z12,z802,z5,z6]),(0,[z184,z3,z8,z232,z5,z6]),(0,[z177,z2,z3,z246,z5,z6]),(0,[z138,z2,z3,z4,z5,z43])]],
   [[(0,[z2,z1011,z8,z4,z5,z6]),(0,[z2,z1012,z8,z4,z5,z6]),(0,[z2,z3,z1013,z4,z5,z6]),(0,[z508,z3,z8,z4,z66,z6]),(0,[z2,z142,z248,z4,z5,z6]),(0,[z2,z3,z1014,z4,z5,z6]),(0,[z1015,z3,z8,z4,z5,z6]),(0,[z231,z2,z8,z4,z5,z58]),(0,[z494,z2,z3,z4,z5,z43]),(0,[z287,z2,z3,z21,z5,z6]),(0,[z2,z3,z4,z5,z6,z1016])],[(0,[z2,z3,z60,z5,z146,z6]),(0,[z2,z3,z4,z141,z117,z183])],[(0,[z397,z27,z8,z4,z5,z6]),(0,[z2,z3,z4,z5,z1017,z6]),(0,[z175,z3,z764,z4,z5,z6]),(1,[z2,z8,z810,z5,z6]),(0,[z2,z3,z1018,z4,z5,z6]),(0,[z177,z0,z87,z2,z3,z6]),(0,[z2,z3,z20,z4,z5,z159]),(0,[z2,z3,z213,z4,z739,z6])],[(0,[z2,z3,z1019,z4,z5,z6]),(0,[z2,z3,z8,z4,z5,z1020]),(0,[z1021,z2,z3,z8,z4,z6]),(0,[z65,z3,z8,z4,z80,z6]),(0,[z1022,z3,z8,z4,z5,z6]),(0,[z294,z158,z8,z4,z5,z6]),(0,[z2,z158,z8,z4,z149,z6]),(0,[z2,z3,z8,z4,z759,z6]),(0,[z1023,z3,z8,z4,z5,z6]),(0,[z2,z1024,z8,z4,z5,z6])]],
   [[(0,[z23,z57,z8,z4,z24,z6]),(0,[z2,z3,z8,z172,z5,z6]),(0,[z2,z3,z4,z5,z1025,z6]),(0,[z2,z3,z8,z5,z6,z1026]),(0,[z2,z8,z4,z5,z6,z1027])],[(0,[z231,z2,z8,z4,z24,z6]),(0,[z2,z3,z8,z4,z5,z1028]),(0,[z2,z1029,z8,z4,z5,z6]),(0,[z2,z864,z26,z4,z5,z6]),(0,[z2,z3,z8,z1030,z5,z6]),(0,[z2,z3,z8,z5,z1031,z6])],[(0,[z2,z3,z4,z1032,z5,z6]),(0,[z13,z3,z8,z4,z5,z59]),(0,[z406,z2,z3,z8,z75,z6]),(0,[z0,z2,z3,z4,z739,z6])],[(1,[z3,z8,z802,z5,z6]),(0,[z2,z3,z8,z802,z5,z6]),(0,[z2,z3,z8,z483,z122,z6]),(0,[z2,z258,z8,z4,z188,z6]),(0,[z2,z8,z4,z5,z205,z559]),(0,[z2,z3,z20,z4,z5,z788])]],
   [[(0,[z2,z3,z8,z1033,z5,z6]),(0,[z2,z8,z4,z5,z6,z67]),(0,[z186,z3,z8,z4,z5,z274]),(0,[z2,z3,z8,z4,z1034,z6]),(0,[z1035,z3,z8,z4,z5,z6])],[(0,[z2,z3,z8,z4,z1036,z6]),(0,[z2,z1037,z8,z4,z5,z6]),(0,[z186,z3,z8,z4,z5,z765]),(0,[z2,z248,z864,z4,z5,z6]),(1,[z2,z8,z4,z827,z6]),(0,[z2,z8,z4,z827,z188,z6])],[(0,[z2,z3,z8,z4,z1038,z6]),(0,[z57,z734,z8,z4,z5,z6]),(0,[z2,z3,z8,z5,z6,z1039]),(0,[z2,z3,z8,z483,z108,z6]),(0,[z0,z287,z2,z3,z4,z6]),(0,[z2,z3,z309,z4,z141,z117])],[(0,[z2,z3,z8,z4,z1040,z6]),(0,[z2,z3,z1041,z4,z5,z6]),(0,[z87,z2,z3,z8,z88,z6]),(0,[z2,z3,z8,z4,z5,z733])]],
   [[(0,[z2,z3,z8,z4,z1042,z6]),(0,[z294,z3,z8,z4,z149,z6]),(0,[z2,z3,z340,z4,z5,z6]),(0,[z406,z2,z3,z60,z8,z6]),(0,[z287,z2,z3,z213,z8,z6]),(0,[z300,z87,z2,z3,z4,z6])],[(0,[z2,z91,z8,z4,z5,z6]),(0,[z2,z273,z8,z4,z5,z692]),(0,[z1043,z2,z3,z8,z5,z6]),(0,[z2,z1044,z8,z4,z5,z6]),(0,[z2,z3,z1045,z4,z5,z6]),(0,[z538,z3,z8,z12,z5,z6]),(0,[z182,z2,z8,z810,z5,z6]),(0,[z2,z3,z156,z4,z149,z6])],[(0,[z2,z8,z4,z24,z205,z6]),(0,[z2,z1046,z8,z4,z5,z6]),(0,[z2,z3,z8,z1047,z5,z6]),(0,[z2,z258,z8,z4,z80,z6]),(0,[z13,z3,z15,z4,z5,z59]),(0,[z2,z400,z248,z4,z5,z6]),(1,[z2,z3,z776,z5,z6]),(0,[z2,z3,z1048,z4,z5,z6])],[(0,[z2,z3,z8,z1049,z5,z6]),(0,[z231,z184,z8,z4,z5,z58]),(0,[z2,z3,z303,z4,z149,z6]),(0,[z2,z3,z76,z5,z6,z606]),(0,[z2,z3,z8,z1050,z5,z6])]],
   [[(0,[z2,z3,z8,z4,z1051,z6]),(0,[z13,z29,z8,z4,z5,z59]),(0,[z123,z2,z864,z4,z5,z6]),(0,[z182,z2,z8,z115,z5,z6])],[(0,[z2,z3,z8,z4,z1052,z6]),(0,[z120,z65,z3,z8,z80,z6]),(0,[z2,z3,z8,z5,z6,z1053]),(0,[z2,z3,z8,z4,z1054,z6])],[(0,[z186,z3,z8,z4,z5,z671]),(0,[z65,z3,z8,z4,z784,z6]),(0,[z2,z3,z8,z1055,z5,z6]),(0,[z2,z3,z8,z1056,z5,z6])],[(0,[z2,z3,z8,z1057,z5,z6]),(0,[z2,z3,z8,z1058,z5,z6]),(0,[z2,z8,z4,z5,z6,z1059]),(0,[z2,z3,z8,z75,z5,z528]),(0,[z0,z2,z3,z312,z4,z6])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 4 128 bkB c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 557) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 557).take 469) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1026)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [557, 469] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_nil pbend))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 91).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 91).take 37).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 128)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [91, 37] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_nil pcend))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 4) (nb2 := 128) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_43156

theorem PEqualNP.Outside.L_meta_43156 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808362 * 2 ^ 32 + 3941132800) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808362 * 2 ^ 32 + 3941132800) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_43156.solve