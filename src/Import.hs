module Import(module Import) where
{
    -- base
    import Data.Bool as Import;
    import Data.Eq as Import;
    import Data.Maybe as Import;
    import Data.Either as Import;
    import Data.Tuple as Import;
    import Data.Functor as Import;
    import Control.Category as Import;
    import Control.Applicative as Import;
    import Control.Monad as Import (Monad(..),MonadPlus(..));

    -- transformers
    import Data.Functor.Identity as Import;
    import Data.Functor.Compose as Import;

    -- witness
    import Data.Witness.EqualType as Import;
    import Data.Witness.SimpleWitness as Import;
    import Data.Witness.List as Import;


    -- constraints
    import Data.Constraint as Import(Dict(..));
}
