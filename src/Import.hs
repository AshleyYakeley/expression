module Import(module Import) where
{
    -- base
    import Data.Bool as Import;
    import Data.Eq as Import;
    import Data.Maybe as Import;
    import Data.Either as Import;
    import Data.Tuple as Import;
    import Data.Foldable as Import;
    import Data.Functor as Import;
    import Control.Category as Import;
    import Control.Applicative as Import;
    import Control.Monad as Import (Monad(..),MonadPlus(..));
    import Data.Proxy as Import;
    import Data.Type.Equality as Import hiding (sym);

    -- transformers
    import Data.Functor.Identity as Import;
    import Data.Functor.Compose as Import;

    -- witness
    import Data.Witness.List as Import;

    -- categories
    import Data.Semigroupoid.Dual as Import;

    -- constraints
    import Data.Constraint as Import(Dict(..));
}
