@tensor
record Pair where
  { a : Real
  , b : Real
  }

minBound : Pair
minBound = { a = 0, b = 0 }

maxBound : Pair
maxBound = { a = 10, b = 10 }

add = minBound + maxBound

@network
f : Pair -> Pair

@property
p : Bool
p = (forall x . minBound <= x <= add => (f x).a >= x.a)

-- @property
-- simple : Bool
-- simple = forall x . 0 <= x.a <= 1 => x.b <= (f x).b

@property
parallel : Bool
parallel = (forall x . 0 < x < 1 => f x >= 0) and (exists y . 0 < y < 1 and f y >= 5)
