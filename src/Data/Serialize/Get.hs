{-# LANGUAGE CPP        #-}
{-# LANGUAGE MagicHash  #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-----------------------------------------------------------------------------
-- |
-- Module      : Data.Serialize.Get
-- Copyright   : Lennart Kolmodin, Galois Inc. 2009
-- License     : BSD3-style (see LICENSE)
--
-- Maintainer  : Trevor Elliott <trevor@galois.com>
-- Stability   :
-- Portability :
--
-- The Get monad. A monad for efficiently building structures from
-- strict ByteStrings
--
-----------------------------------------------------------------------------

#if defined(__GLASGOW_HASKELL__) && !defined(__HADDOCK__)
#include "MachDeps.h"
#endif

module Data.Serialize.Get (

    -- * The Get type
      Get
    , runGet
    , runGetLazy
    , runGetState
    , runGetLazyState

    -- ** Incremental interface
    , Result(..)
    , runGetPartial
    , runGetChunk

    -- * Parsing
    , ensure
    , ensure_
    , isolate
    , isolate'
    , label
    , (<?>)
    , skip
    , uncheckedSkip
    , matchParsed
    , lookAhead
    , lookAheadM
    , lookAheadE
    , uncheckedLookAhead

    -- * Utility
    , getBytes
    , getBuffer
    , remaining
    , bytesRead
    , isEmpty

    -- * Parsing particular types
    , getWord8
    , getInt8

    -- ** ByteStrings
    , getByteString
    , getLazyByteString
    , getShortByteString

    -- ** Big-endian reads
    , getWord16be
    , getWord32be
    , getWord64be
    , getInt16be
    , getInt32be
    , getInt64be

    -- ** Little-endian reads
    , getWord16le
    , getWord32le
    , getWord64le
    , getInt16le
    , getInt32le
    , getInt64le

    -- ** Host-endian, unaligned reads
    , getWordhost
    , getWord16host
    , getWord32host
    , getWord64host

    -- ** Containers
    , getTwoOf
    , getListOf
    , getIArrayOf
    , getTreeOf
    , getSeqOf
    , getMapOf
    , getIntMapOf
    , getSetOf
    , getIntSetOf
    , getMaybeOf
    , getEitherOf
    , getNested
  ) where

import qualified Control.Applicative as A
import qualified Control.Monad as M
import qualified Control.Monad.Fail as Fail
import Data.Semigroup (Semigroup(..))
import Data.Array.IArray (IArray,listArray)
import Data.Ix (Ix)
import Data.List (intercalate)
import Data.Maybe (isNothing, fromMaybe)
import Data.Either (isLeft)
import Foreign
import System.IO.Unsafe (unsafeDupablePerformIO)

import qualified Data.ByteString          as B
import qualified Data.ByteString.Internal as B
import qualified Data.ByteString.Unsafe   as B
import qualified Data.ByteString.Lazy     as L
import qualified Data.ByteString.Lazy.Internal as L
import qualified Data.ByteString.Short    as BS
import qualified Data.IntMap              as IntMap
import qualified Data.IntSet              as IntSet
import qualified Data.Map                 as Map
import qualified Data.Sequence            as Seq
import qualified Data.Set                 as Set
import qualified Data.Tree                as T

import qualified Data.Serialize.Buffer as Buf
import Data.Serialize.Buffer (Buffer)

#if defined(__GLASGOW_HASKELL__) && !defined(__HADDOCK__)
import GHC.Base
import GHC.Word
#endif

-- | The result of a parse.
data Result r = Fail String B.ByteString
              -- ^ The parse failed. The 'String' is the
              --   message describing the error, if any.
              | Partial (B.ByteString -> Result r)
              -- ^ Supply this continuation with more input so that
              --   the parser can resume. To indicate that no more
              --   input is available, use an 'B.empty' string.
              | Done r B.ByteString
              -- ^ The parse succeeded.  The 'B.ByteString' is the
              --   input that had not yet been consumed (if any) when
              --   the parse succeeded.

instance Show r => Show (Result r) where
    show (Fail msg _) = "Fail " ++ show msg
    show (Partial _)  = "Partial _"
    show (Done r bs)  = "Done " ++ show r ++ " " ++ show bs

instance Functor Result where
    fmap _ (Fail msg rest) = Fail msg rest
    fmap f (Partial k)     = Partial (fmap f . k)
    fmap f (Done r bs)     = Done (f r) bs

newtype Pos = Pos {fromPos :: Int}
  deriving (Eq, Ord, Num, Enum, Bounded, Show)

-- | The Get monad is an Exception and State monad.
newtype Get a = Get
  { unGet :: forall r. Buffer -> Pos -> More
                    -> Failure r -> Success a r
                    -> Result r
  }

type Failure   r = Buffer -> Pos -> More -> [String] -> String -> Result r
type Success a r = Buffer -> Pos -> More -> a                  -> Result r

-- | Have we read all available input?
data More
  = Complete
  | Incomplete (Maybe Int)
    deriving (Eq)

moreLength :: More -> Int
moreLength m = case m of
  Complete      -> 0
  Incomplete mb -> fromMaybe 0 mb
{-# INLINE moreLength #-}


instance Functor Get where
    fmap p m = Get $ \ b0 p0 m0 kf ks ->
      let ks' b1 p1 m1 a = ks b1 p1 m1 (p a)
      in unGet m b0 p0 m0 kf ks'
    {-# INLINE fmap #-}
      -- unGet m s0 b0 m0 kf $ \ b1 p1 m1 a     -> ks b1 p1 m1 (p a)

-- apP :: Get (a -> b) -> Get a -> Get b
-- apP d e = do
--   b <- d
--   a <- e
--   return (b a)
-- {-# INLINE apP #-}

apP :: Get (a -> b) -> Get a -> Get b
apP f x =             Get $ \ b0 p0 m0 kf ks ->
      unGet f b0 p0 m0 kf $ \ b1 p1 m1 g     ->
      unGet x b1 p1 m1 kf $ \ b2 p2 m2 y     -> ks b2 p2 m2 (g y)
{-# INLINE apP #-}

plus :: Get a -> Get a -> Get a
plus f g = Get $ \b0 !p0 m0 kf ks ->
  let kf' b1 _ m1 _ _ = unGet g b1 p0 m1 kf ks
  in unGet f b0 p0 m0 kf' ks
{-# INLINE plus #-}

instance M.MonadPlus Get where
    mzero = failDesc "mzero"

    mplus = plus
    {-# INLINE mplus #-}

instance A.Applicative Get where
    pure a = Get $ \ b0 p0 m0 _ ks -> ks b0 p0 m0 a
    {-# INLINE pure #-}

    (<*>) = apP
      -- Get $ \ s0 b0 m0 kf ks ->
      -- unGet f s0 b0 m0 kf $ \ s1 b1 m1 g     ->
      -- unGet x s1 b1 m1 kf $ \ s2 b2 m2 y     -> ks s2 b2 m2 (g y)
    {-# INLINE (<*>) #-}

    m *> k = m >>= \_ -> k
      -- Get $ \ s0 b0 m0 kf ks ->
      -- unGet m s0 b0 m0 kf $ \ s1 b1 m1 _     -> unGet k s1 b1 m1 kf ks
    {-# INLINE (*>) #-}

    x <* y = x >>= \a -> y >> pure a
    {-# INLINE (<*) #-}

instance Semigroup (Get a) where
    (<>) = plus
    {-# INLINE (<>) #-}

instance Monoid (Get a) where
    mempty  = fail "mempty"
    {-# INLINE mempty #-}
    mappend = (<>)
    {-# INLINE mappend #-}

instance A.Alternative Get where
    empty = failDesc "empty"
    {-# INLINE empty #-}

    (<|>) = plus
    {-# INLINE (<|>) #-}

instance Fail.MonadFail Get where
    fail err = Get $ \b0 p0 m0 kf _ -> kf b0 p0 m0 [] msg
      where msg = "Failed reading: " ++ err
    {-# INLINE fail #-}

-- Definition directly from Control.Monad.State.Strict
instance Monad Get where
    fail = Fail.fail
    {-# INLINE fail #-}

    return = A.pure
    {-# INLINE return #-}

    m >>= g = Get $ \ b0 !p0 m0 kf ks ->
      let ks' b1 !p1 m1 a = unGet (g a) b1 p1 m1 kf ks
      in unGet m b0 p0 m0 kf ks'
        -- unGet m b0 p0 m0 kf $ \ s1 b1 m1 a     -> unGet (g a) s1 b1 m1 kf ks
    {-# INLINE (>>=) #-}

    (>>) = (A.*>)
    {-# INLINE (>>) #-}

------------------------------------------------------------------------

unsafeSubstring :: Pos -> Pos -> Buffer -> B.ByteString
unsafeSubstring (Pos pos) (Pos n) = Buf.unsafeSubstring pos n
{-# INLINE unsafeSubstring #-}

formatTrace :: [String] -> String
formatTrace [] = "Empty call stack"
formatTrace ls = "From:\t" ++ intercalate "\n\t" ls ++ "\n"

label :: String -> Get a -> Get a
label l m = Get $ \ b0 p0 m0 kf ks ->
  let kf' b1 _ m1 ls = kf b1 p0 m1 (l:ls)
  in unGet m b0 p0 m0 kf' ks
{-# INLINE label #-}

(<?>) :: Get a -> String -> Get a
g <?> msg0 = label msg0 g
{-# INLINE (<?>) #-}
infix 0 <?>

finalK :: Success a a
finalK buf (Pos pos) _ a = Done a (Buf.unsafeDrop pos buf)

failK :: Failure a
failK b (Pos pos) _ ls msg =
  Fail (unlines [msg, formatTrace ls]) (Buf.unsafeDrop pos b)

-- | Run the Get monad applies a 'get'-based parser on the input ByteString
runGet :: Get a -> B.ByteString -> Either String a
runGet m str =
  case unGet m (Buf.buffer str) (Pos 0) Complete failK finalK of
    Fail i _  -> Left i
    Done a _  -> Right a
    Partial{} -> Left "Failed reading: Internal error: unexpected Partial."
{-# INLINE runGet #-}

-- | Run the get monad on a single chunk, providing an optional length for the
-- remaining, unseen input, with Nothing indicating that it's not clear how much
-- input is left.  For example, with a lazy ByteString, the optional length
-- represents the sum of the lengths of all remaining chunks.
runGetChunk :: Get a -> Maybe Int -> B.ByteString -> Result a
runGetChunk m mbLen str = unGet m (Buf.buffer str) (Pos 0) (Incomplete mbLen) failK finalK
{-# INLINE runGetChunk #-}

-- | Run the Get monad applies a 'get'-based parser on the input ByteString
runGetPartial :: Get a -> B.ByteString -> Result a
runGetPartial g = runGetChunk g Nothing
{-# INLINE runGetPartial #-}

-- | Run the Get monad applies a 'get'-based parser on the input
-- ByteString. Additional to the result of get it returns the number of
-- consumed bytes and the rest of the input.
runGetState :: Get a -> B.ByteString -> Int
            -> Either String (a, B.ByteString)
runGetState m str off = case runGetState' m str off of
  (Right a,bs) -> Right (a,bs)
  (Left i,_)   -> Left i
{-# INLINE runGetState #-}

-- | Run the Get monad applies a 'get'-based parser on the input
-- ByteString. Additional to the result of get it returns the number of
-- consumed bytes and the rest of the input, even in the event of a failure.
runGetState' :: Get a -> B.ByteString -> Int
             -> (Either String a, B.ByteString)
runGetState' m str off =
  case unGet m (Buf.buffer (B.drop off str)) (Pos 0) Complete failK finalK of
    Fail i bs -> (Left i,bs)
    Done a bs -> (Right a, bs)
    Partial{} -> (Left "Failed reading: Internal error: unexpected Partial.",B.empty)
{-# INLINE runGetState' #-}


-- Lazy Get --------------------------------------------------------------------

runGetLazy'' :: Get a -> L.ByteString -> Result a
runGetLazy'' m str =
  case str of
    L.Chunk x xs -> go (runGetChunk m (Just (fromIntegral $ L.length str)) x) xs
    e            -> go (runGetPartial m B.empty) e
  where
    go (Fail msg x) ys            = Fail msg (L.toStrict $ L.chunk x ys)
    go (Done r x) ys              = Done r (L.toStrict $ L.chunk x ys)
    go (Partial k) (L.Chunk y ys) = go (k y) ys
    go (Partial k) e              = go (k B.empty) e
{-# INLINE runGetLazy'' #-}

-- | Run the Get monad over a Lazy ByteString.  Note that this will not run the
-- Get parser lazily, but will operate on lazy ByteStrings.
runGetLazy :: Get a -> L.ByteString -> Either String a
runGetLazy m lstr = case runGetLazy'' m lstr of
  Done r _   -> Right r
  Fail msg _ -> Left msg
  _          -> undefined
{-# INLINE runGetLazy #-}

-- | Run the Get monad over a Lazy ByteString.  Note that this does not run the
-- Get parser lazily, but will operate on lazy ByteStrings.
runGetLazyState :: Get a -> L.ByteString -> Either String (a,L.ByteString)
runGetLazyState m lstr = case runGetLazy'' m lstr of
  Done r x   -> Right (r, L.fromChunks [x])
  Fail msg _ -> Left msg
  _          -> undefined
{-# INLINE runGetLazyState #-}

------------------------------------------------------------------------

lengthAtLeast :: Pos -> Int -> Buffer -> Bool
lengthAtLeast (Pos pos) n bs = Buf.length bs >= pos + n
{-# INLINE lengthAtLeast #-}

advance :: Int -> Get ()
advance !n = Get $ \buf pos more _ ks ->
  ks buf (pos + Pos n) more ()
{-# INLINE advance #-}

-- | Ask for input.  If we receive any, pass the augmented input to a
-- success continuation, otherwise to a failure continuation.
prompt :: Buffer -> Pos -> More
       -> (Buffer -> Pos -> More -> Result r)
       -> (Buffer -> Pos -> More -> Result r)
       -> Result r
prompt buf pos more lose ks = Partial $ \s ->
  if B.length s == 0
      then lose buf pos Complete
      else
        let mbMore (Incomplete x) = x
            mbMore _              = Nothing
        in ks (buf `Buf.pappend` s) pos (Incomplete $ mbMore more)
{-# INLINE prompt #-}

-- | Immediately demand more input via a 'Partial' continuation
-- result.
demandInput :: Get ()
demandInput = Get $ \b0 p0 !m0 kf ks ->
  case m0 of
    Complete -> kf b0 p0 m0 [] "not enough input"
    _ -> let kf' _ p1 m1 = kf b0 p1 m1 [] "not enough input"
             ks' b1 p1 m1 = ks b1 p1 m1 ()
         in prompt b0 p0 m0 kf' ks'
{-# INLINE demandInput #-}

{-# INLINE ensureSuspended #-}
ensureSuspended :: Int -> Buffer -> Pos -> More
                -> Failure r
                -> Success B.ByteString r
                -> Result r
ensureSuspended n b0 p0 = unGet (demandInput >> go) b0 p0
  where go = Get $ \b1 p1 m1 kf' ks' ->
          if lengthAtLeast p1 n b1
              then ks' b1 p1 m1 (unsafeSubstring p0 (Pos n) b1)
              else unGet (demandInput >> go) b1 p1 m1 kf' ks'

{-# INLINE ensureSuspended_ #-}
ensureSuspended_ :: Int -> Buffer -> Pos -> More
                 -> Failure r
                 -> Success () r
                 -> Result r
ensureSuspended_ n = unGet (demandInput >> go)
  where go = Get $ \b1 p1 m1 kf' ks' ->
          if lengthAtLeast p1 n b1
              then ks' b1 p1 m1 ()
              else unGet (demandInput >> go) b1 p1 m1 kf' ks'

{-# INLINE ensureSuspendedBuf #-}
ensureSuspendedBuf :: Int -> Buffer -> Pos -> More
                   -> Failure r
                   -> Success Buffer r
                   -> Result r
ensureSuspendedBuf n b0 p0 = unGet (demandInput >> go) b0 p0
  where go = Get $ \b1 p1 m1 kf' ks' ->
          if lengthAtLeast p1 n b1
              then ks' b1 p1 m1 (Buf.unsafeShrink (fromPos p0) n b1)
              else unGet (demandInput >> go) b1 p1 m1 kf' ks'

-- | If at least @n@ bytes of input are available, return the current
--   input, otherwise fail.
ensure :: Int -> Get B.ByteString
ensure n0 = n0 `seq` Get $ \ b0 p0 m0 kf ks ->
  if lengthAtLeast p0 n0 b0
      then ks b0 p0 m0 (unsafeSubstring p0 (Pos n0) b0)
      else ensureSuspended n0 b0 p0 m0 kf ks
{-# INLINE ensure #-}

-- | If at least @n@ bytes of input are available, succeed,
--   otherwise fail.
ensure_ :: Int -> Get ()
ensure_ n0 = n0 `seq` Get $ \ b0 p0 m0 kf ks ->
  if lengthAtLeast p0 n0 b0
      then ks b0 p0 m0 ()
      else ensureSuspended_ n0 b0 p0 m0 kf ks
{-# INLINE ensure_ #-}

-- | If at least @n@ bytes of input are available, succeed,
--   otherwise fail.
ensureBuf :: Int -> Get Buf.Buffer
ensureBuf n0 = n0 `seq` Get $ \ b0 p0 m0 kf ks ->
  if lengthAtLeast p0 n0 b0
      then ks b0 p0 m0 (Buf.unsafeShrink (fromPos p0) n0 b0)
      else ensureSuspendedBuf n0 b0 p0 m0 kf ks
{-# INLINE ensureBuf #-}

-- | Return bytes read till now.
bytesRead :: Get Int
bytesRead = Get $ \b0 !p0 m0 _ ks -> ks b0 p0 m0 (fromPos p0)
{-# INLINE bytesRead #-}

-- | Isolate an action to operating within a fixed block of bytes.  The action
--   is required to consume all the bytes that it is isolated to.
isolate :: Int -> Get a -> Get a
isolate n m = Get $ \b0 !p0 m0 kf ks ->
  let ks' b1 !p1 m1 a =
        if p1 - p0 == Pos n
          then ks b1 p1 m1 a
          else kf b1 p0 m1 [] "isolate: not all bytes parsed"
  in unGet (isolate' n m) b0 p0 m0 kf ks'
{-# INLINE isolate #-}

  -- | Isolate an action to operating within a fixed block of bytes.  Unlike
  --   isolate, isolate' doesn't require action to consume all the bytes.
isolate' :: Int -> Get a -> Get a
isolate' n g
    | n >= 0 = ensure_ n >> go
    | otherwise = fail "isolate': negative n"
  where
    go = Get $ \b0 p0 m0 kf ks ->
      let ks' _ = ks b0
          !buf' = Buf.unsafeShrink 0 (fromPos p0 + n) b0
      in unGet g buf' p0 m0 kf ks'
{-# INLINE isolate' #-}

matchParsed :: Get a -> Get (a, Int)
matchParsed g = Get $ \b0 p0 m0 kf ks ->
  let ks' b1 p1 m1 a = ks b1 p1 m1 (a, fromPos (p1 - p0))
  in unGet g b0 p0 m0 kf ks'
{-# INLINE matchParsed #-}

failDesc :: String -> Get a
failDesc err = Get $ \b0 p0 m0 kf _ ->
    let !msg = "Failed reading: " ++ err
    in kf b0 p0 m0 [] msg

-- | Skip ahead @n@ bytes. Fails if fewer than @n@ bytes are available.
skip :: Int -> Get ()
skip n = ensure_ n >> advance n
{-# INLINE skip #-}

-- | Skip ahead up to @n@ bytes in the current chunk. No error if there aren't
-- enough bytes, or if less than @n@ bytes are skipped.
uncheckedSkip :: Int -> Get ()
uncheckedSkip !n = Get $ \b0 p0 m0 _ ks ->
  case Buf.length b0 of
    len | len >= n + fromPos p0 -> ks b0 (p0 + Pos n) m0 ()
        | otherwise -> ks b0 (Pos (Buf.length b0)) m0 ()
{-# INLINE uncheckedSkip #-}

-- | Run @ga@, but return without consuming its input.
-- Fails if @ga@ fails.
lookAhead :: Get a -> Get a
lookAhead ga = Get $ \ b0 p0 m0 kf ks ->
  -- the new continuation extends the old input with the new buffered bytes, and
  -- appends the new buffer to the old one, if there was one.
  let ks' b1 _ _ = ks b1 p0 m0
      kf' b1 _ _ = kf b1 p0 m0
   in unGet ga b0 p0 m0 kf' ks'

-- | Like 'lookAhead', but consume the input if @gma@ returns 'Just _'.
-- Fails if @gma@ fails.
lookAheadM :: Get (Maybe a) -> Get (Maybe a)
lookAheadM gma = Get $ \ b0 p0 m0 kf ks ->
  let ks' b1 p1 _ a = ks b1 (if isNothing a then p0 else p1) m0 a
      kf' b1 _ _ = kf b1 p0 m0
   in unGet gma b0 p0 m0 kf' ks'

-- | Like 'lookAhead', but consume the input if @gea@ returns 'Right _'.
-- Fails if @gea@ fails.
lookAheadE :: Get (Either a b) -> Get (Either a b)
lookAheadE gea = Get $ \ b0 p0 m0 kf ks ->
  let ks' b1 p1 _ a = ks b1 (if isLeft a then p0 else p1) m0 a
      kf' b1 _ _ = kf b1 p0 m0
   in unGet gea b0 p0 m0 kf' ks'

-- | Get the next up to @n@ bytes as a ByteString until end of this chunk,
-- without consuming them.
uncheckedLookAhead :: Int -> Get B.ByteString
uncheckedLookAhead !n = Get $ \b0 p0 m0 _ ks -> ks b0 p0 m0 (Buf.substring (fromPos p0) n b0)

------------------------------------------------------------------------
-- Utility

-- | Get the number of remaining unparsed bytes.  Useful for checking whether
-- all input has been consumed.
--
-- WARNING: when run with @runGetPartial@, remaining will only return the number
-- of bytes that are remaining in the current input.
remaining :: Get Int
remaining = Get $ \ b0 p0 !m0 _ ks -> ks b0 p0 m0 (max (Buf.length b0) (moreLength m0) - fromPos p0)
{-# INLINE remaining #-}

-- | Test whether all input has been consumed.
--
-- WARNING: when run with @runGetPartial@, isEmpty will only tell you if you're
-- at the end of the current chunk.
isEmpty :: Get Bool
isEmpty = Get $ \ b0 p0 !m0 _ ks -> ks b0 p0 m0 (fromPos p0 == max (Buf.length b0) (moreLength m0))
{-# INLINE isEmpty #-}

------------------------------------------------------------------------
-- Utility with ByteStrings

-- | An efficient 'get' method for strict ByteStrings. Fails if fewer
-- than @n@ bytes are left in the input. This function creates a fresh
-- copy of the underlying bytes.
getByteString :: Int -> Get B.ByteString
getByteString n = do
  bs <- getBytes n
  return $! B.copy bs

getLazyByteString :: Int64 -> Get L.ByteString
getLazyByteString n = f `fmap` getByteString (fromIntegral n)
  where f bs = L.fromChunks [bs]

getShortByteString :: Int -> Get BS.ShortByteString
getShortByteString n = do
  bs <- getBytes n
  return $! BS.toShort bs


------------------------------------------------------------------------
-- Helpers

-- | Pull @n@ bytes from the input, as a strict ByteString, without copying.
getBytes :: Int -> Get B.ByteString
getBytes n | n < 0 = fail "getBytes: negative length requested"
getBytes n = ensure n <* advance n
{-# INLINE getBytes #-}

-- | Pull @n@ bytes from the input, as a Buffer.
getBuffer :: Int -> Get Buf.Buffer
getBuffer n | n < 0 = fail "getBuffer: negative length requested"
getBuffer n = getBuffer' n
{-# INLINE getBuffer #-}

-- | Ensure @n@ bytes from the input, return an underlying Buffer.
getBuffer' :: Int -> Get Buf.Buffer
getBuffer' !n0 = Get $ \ b0 p0 m0 kf ks ->
  let ks' b1 p1 = ks b1 (p1 + Pos n0)
  in unGet (ensureBuf n0) b0 p0 m0 kf ks'
{-# INLINE getBuffer' #-}

------------------------------------------------------------------------
-- Primtives

-- helper, get a raw Ptr onto a strict ByteString copied out of the
-- underlying strict byteString.

getPtr :: Storable a => Int -> Get a
getPtr n = do
    (fp,o,_) <- Buf.toForeignPtr `fmap` getBuffer n
    let k p = peek (castPtr (p `plusPtr` o))
    return (unsafeDupablePerformIO (withForeignPtr fp k))
{-# INLINE getPtr #-}

-----------------------------------------------------------------------

-- | Read a Int8 from the monad state
getInt8 :: Get Int8
getInt8 = do
    s <- getBuffer' 1
    return $! fromIntegral (Buf.unsafeHead s)

-- | Read a Int16 in big endian format
getInt16be :: Get Int16
getInt16be = do
    s <- getBuffer' 2
    return $! (fromIntegral (s `Buf.unsafeIndex` 0) `shiftL` 8) .|.
              (fromIntegral (s `Buf.unsafeIndex` 1) )

-- | Read a Int16 in little endian format
getInt16le :: Get Int16
getInt16le = do
    s <- getBuffer' 2
    return $! (fromIntegral (s `Buf.unsafeIndex` 1) `shiftL` 8) .|.
              (fromIntegral (s `Buf.unsafeIndex` 0) )

-- | Read a Int32 in big endian format
getInt32be :: Get Int32
getInt32be = do
    s <- getBuffer' 4
    return $! (fromIntegral (s `Buf.unsafeIndex` 0) `shiftL` 24) .|.
              (fromIntegral (s `Buf.unsafeIndex` 1) `shiftL` 16) .|.
              (fromIntegral (s `Buf.unsafeIndex` 2) `shiftL`  8) .|.
              (fromIntegral (s `Buf.unsafeIndex` 3) )

-- | Read a Int32 in little endian format
getInt32le :: Get Int32
getInt32le = do
    s <- getBuffer' 4
    return $! (fromIntegral (s `Buf.unsafeIndex` 3) `shiftL` 24) .|.
              (fromIntegral (s `Buf.unsafeIndex` 2) `shiftL` 16) .|.
              (fromIntegral (s `Buf.unsafeIndex` 1) `shiftL`  8) .|.
              (fromIntegral (s `Buf.unsafeIndex` 0) )

-- | Read a Int64 in big endian format
getInt64be :: Get Int64
getInt64be = do
    s <- getBuffer' 8
    return $! (fromIntegral (s `Buf.unsafeIndex` 0) `shiftL` 56) .|.
              (fromIntegral (s `Buf.unsafeIndex` 1) `shiftL` 48) .|.
              (fromIntegral (s `Buf.unsafeIndex` 2) `shiftL` 40) .|.
              (fromIntegral (s `Buf.unsafeIndex` 3) `shiftL` 32) .|.
              (fromIntegral (s `Buf.unsafeIndex` 4) `shiftL` 24) .|.
              (fromIntegral (s `Buf.unsafeIndex` 5) `shiftL` 16) .|.
              (fromIntegral (s `Buf.unsafeIndex` 6) `shiftL`  8) .|.
              (fromIntegral (s `Buf.unsafeIndex` 7) )

-- | Read a Int64 in little endian format
getInt64le :: Get Int64
getInt64le = do
    s <- getBuffer' 8
    return $! (fromIntegral (s `Buf.unsafeIndex` 7) `shiftL` 56) .|.
              (fromIntegral (s `Buf.unsafeIndex` 6) `shiftL` 48) .|.
              (fromIntegral (s `Buf.unsafeIndex` 5) `shiftL` 40) .|.
              (fromIntegral (s `Buf.unsafeIndex` 4) `shiftL` 32) .|.
              (fromIntegral (s `Buf.unsafeIndex` 3) `shiftL` 24) .|.
              (fromIntegral (s `Buf.unsafeIndex` 2) `shiftL` 16) .|.
              (fromIntegral (s `Buf.unsafeIndex` 1) `shiftL`  8) .|.
              (fromIntegral (s `Buf.unsafeIndex` 0) )

{-# INLINE getInt8    #-}
{-# INLINE getInt16be #-}
{-# INLINE getInt16le #-}
{-# INLINE getInt32be #-}
{-# INLINE getInt32le #-}
{-# INLINE getInt64be #-}
{-# INLINE getInt64le #-}

------------------------------------------------------------------------

-- | Read a Word8 from the monad state
getWord8 :: Get Word8
getWord8 = do
    s <- getBuffer' 1
    return $! Buf.unsafeHead s

-- | Read a Word16 in big endian format
getWord16be :: Get Word16
getWord16be = do
    s <- getBuffer' 2
    return $! (fromIntegral (s `Buf.unsafeIndex` 0) `shiftl_w16` 8) .|.
              (fromIntegral (s `Buf.unsafeIndex` 1))

-- | Read a Word16 in little endian format
getWord16le :: Get Word16
getWord16le = do
    s <- getBuffer' 2
    return $! (fromIntegral (s `Buf.unsafeIndex` 1) `shiftl_w16` 8) .|.
              (fromIntegral (s `Buf.unsafeIndex` 0) )

-- | Read a Word32 in big endian format
getWord32be :: Get Word32
getWord32be = do
    s <- getBuffer' 4
    return $! (fromIntegral (s `Buf.unsafeIndex` 0) `shiftl_w32` 24) .|.
              (fromIntegral (s `Buf.unsafeIndex` 1) `shiftl_w32` 16) .|.
              (fromIntegral (s `Buf.unsafeIndex` 2) `shiftl_w32`  8) .|.
              (fromIntegral (s `Buf.unsafeIndex` 3) )

-- | Read a Word32 in little endian format
getWord32le :: Get Word32
getWord32le = do
    s <- getBuffer' 4
    return $! (fromIntegral (s `Buf.unsafeIndex` 3) `shiftl_w32` 24) .|.
              (fromIntegral (s `Buf.unsafeIndex` 2) `shiftl_w32` 16) .|.
              (fromIntegral (s `Buf.unsafeIndex` 1) `shiftl_w32`  8) .|.
              (fromIntegral (s `Buf.unsafeIndex` 0) )

-- | Read a Word64 in big endian format
getWord64be :: Get Word64
getWord64be = do
    s <- getBuffer' 8
    return $! (fromIntegral (s `Buf.unsafeIndex` 0) `shiftl_w64` 56) .|.
              (fromIntegral (s `Buf.unsafeIndex` 1) `shiftl_w64` 48) .|.
              (fromIntegral (s `Buf.unsafeIndex` 2) `shiftl_w64` 40) .|.
              (fromIntegral (s `Buf.unsafeIndex` 3) `shiftl_w64` 32) .|.
              (fromIntegral (s `Buf.unsafeIndex` 4) `shiftl_w64` 24) .|.
              (fromIntegral (s `Buf.unsafeIndex` 5) `shiftl_w64` 16) .|.
              (fromIntegral (s `Buf.unsafeIndex` 6) `shiftl_w64`  8) .|.
              (fromIntegral (s `Buf.unsafeIndex` 7) )

-- | Read a Word64 in little endian format
getWord64le :: Get Word64
getWord64le = do
    s <- getBuffer' 8
    return $! (fromIntegral (s `Buf.unsafeIndex` 7) `shiftl_w64` 56) .|.
              (fromIntegral (s `Buf.unsafeIndex` 6) `shiftl_w64` 48) .|.
              (fromIntegral (s `Buf.unsafeIndex` 5) `shiftl_w64` 40) .|.
              (fromIntegral (s `Buf.unsafeIndex` 4) `shiftl_w64` 32) .|.
              (fromIntegral (s `Buf.unsafeIndex` 3) `shiftl_w64` 24) .|.
              (fromIntegral (s `Buf.unsafeIndex` 2) `shiftl_w64` 16) .|.
              (fromIntegral (s `Buf.unsafeIndex` 1) `shiftl_w64`  8) .|.
              (fromIntegral (s `Buf.unsafeIndex` 0) )

{-# INLINE getWord8    #-}
{-# INLINE getWord16be #-}
{-# INLINE getWord16le #-}
{-# INLINE getWord32be #-}
{-# INLINE getWord32le #-}
{-# INLINE getWord64be #-}
{-# INLINE getWord64le #-}

------------------------------------------------------------------------
-- Host-endian reads

-- | /O(1)./ Read a single native machine word. The word is read in
-- host order, host endian form, for the machine you're on. On a 64 bit
-- machine the Word is an 8 byte value, on a 32 bit machine, 4 bytes.
getWordhost :: Get Word
getWordhost = getPtr (sizeOf (undefined :: Word))

-- | /O(1)./ Read a 2 byte Word16 in native host order and host endianness.
getWord16host :: Get Word16
getWord16host = getPtr (sizeOf (undefined :: Word16))

-- | /O(1)./ Read a Word32 in native host order and host endianness.
getWord32host :: Get Word32
getWord32host = getPtr  (sizeOf (undefined :: Word32))

-- | /O(1)./ Read a Word64 in native host order and host endianess.
getWord64host   :: Get Word64
getWord64host = getPtr  (sizeOf (undefined :: Word64))

------------------------------------------------------------------------
-- Unchecked shifts

shiftl_w16 :: Word16 -> Int -> Word16
shiftl_w32 :: Word32 -> Int -> Word32
shiftl_w64 :: Word64 -> Int -> Word64

#if defined(__GLASGOW_HASKELL__) && !defined(__HADDOCK__)
shiftl_w16 (W16# w) (I# i) = W16# (w `uncheckedShiftL#`   i)
shiftl_w32 (W32# w) (I# i) = W32# (w `uncheckedShiftL#`   i)

#if WORD_SIZE_IN_BITS < 64
shiftl_w64 (W64# w) (I# i) = W64# (w `uncheckedShiftL64#` i)

#if __GLASGOW_HASKELL__ <= 606
-- Exported by GHC.Word in GHC 6.8 and higher
foreign import ccall unsafe "stg_uncheckedShiftL64"
    uncheckedShiftL64#     :: Word64# -> Int# -> Word64#
#endif

#else
shiftl_w64 (W64# w) (I# i) = W64# (w `uncheckedShiftL#` i)
#endif

#else
shiftl_w16 = shiftL
shiftl_w32 = shiftL
shiftl_w64 = shiftL
#endif


-- Containers ------------------------------------------------------------------

getTwoOf :: Get a -> Get b -> Get (a,b)
getTwoOf ma mb = M.liftM2 (,) ma mb

-- | Get a list in the following format:
--   Word64 (big endian format)
--   element 1
--   ...
--   element n
getListOf :: Get a -> Get [a]
getListOf m = go [] =<< getWord64be
  where
  go as 0 = return $! reverse as
  go as i = do x <- m
               x `seq` go (x:as) (i - 1)

-- | Get an IArray in the following format:
--   index (lower bound)
--   index (upper bound)
--   Word64 (big endian format)
--   element 1
--   ...
--   element n
getIArrayOf :: (Ix i, IArray a e) => Get i -> Get e -> Get (a i e)
getIArrayOf ix e = M.liftM2 listArray (getTwoOf ix ix) (getListOf e)

-- | Get a sequence in the following format:
--   Word64 (big endian format)
--   element 1
--   ...
--   element n
getSeqOf :: Get a -> Get (Seq.Seq a)
getSeqOf m = go Seq.empty =<< getWord64be
  where
  go xs 0 = return $! xs
  go xs n = xs `seq` n `seq` do
              x <- m
              go (xs Seq.|> x) (n - 1)

-- | Read as a list of lists.
getTreeOf :: Get a -> Get (T.Tree a)
getTreeOf m = M.liftM2 T.Node m (getListOf (getTreeOf m))

-- | Read as a list of pairs of key and element.
getMapOf :: Ord k => Get k -> Get a -> Get (Map.Map k a)
getMapOf k m = Map.fromList `fmap` getListOf (getTwoOf k m)

-- | Read as a list of pairs of int and element.
getIntMapOf :: Get Int -> Get a -> Get (IntMap.IntMap a)
getIntMapOf i m = IntMap.fromList `fmap` getListOf (getTwoOf i m)

-- | Read as a list of elements.
getSetOf :: Ord a => Get a -> Get (Set.Set a)
getSetOf m = Set.fromList `fmap` getListOf m

-- | Read as a list of ints.
getIntSetOf :: Get Int -> Get IntSet.IntSet
getIntSetOf m = IntSet.fromList `fmap` getListOf m

-- | Read in a Maybe in the following format:
--   Word8 (0 for Nothing, anything else for Just)
--   element (when Just)
getMaybeOf :: Get a -> Get (Maybe a)
getMaybeOf m = do
  tag <- getWord8
  case tag of
    0 -> return Nothing
    _ -> Just `fmap` m

-- | Read an Either, in the following format:
--   Word8 (0 for Left, anything else for Right)
--   element a when 0, element b otherwise
getEitherOf :: Get a -> Get b -> Get (Either a b)
getEitherOf ma mb = do
  tag <- getWord8
  case tag of
    0 -> Left  `fmap` ma
    _ -> Right `fmap` mb

-- | Read in a length and then read a nested structure
--   of that length.
getNested :: Get Int -> Get a -> Get a
getNested getLen getVal = do
    n <- getLen
    isolate n getVal
