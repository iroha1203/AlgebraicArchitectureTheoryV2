import FixtureOld.AG.Basic

namespace FixtureOld.AG
end FixtureOld.AG

namespace FixtureOld.AG.Smoke
def witness : Nat := 1
end FixtureOld.AG.Smoke
namespace FixtureOld.AG.Shared.Inner
def witness : Nat := 2
end FixtureOld.AG.Shared.Inner

def FixtureOld.AG.Smoke.firstFailingSlot? : Nat := 3
def FixtureOld.AG.Smoke.commit! : Nat := 4
