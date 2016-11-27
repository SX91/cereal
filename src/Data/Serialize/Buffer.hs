{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE MagicHash         #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Rank2Types        #-}
{-# LANGUAGE UnboxedTuples     #-}
module Data.Serialize.Buffer
    (
      Buffer
    , buffer
    , unbuffer
    , toForeignPtr
    , pappend
    , length
    , substring
    , unsafeShrink
    , unsafeHead
    , unsafeIndex
    , unsafeSubstring
    , unsafeDrop
    ) where

import           Control.Exception        (assert)
import           Data.ByteString.Internal (ByteString (..), memcpy,
                                           nullForeignPtr)
import           Data.List                (foldl1')
import           Data.Monoid              as Mon (Monoid (..))
import           Data.Semigroup           (Semigroup (..))
import           Data.Word                (Word8)
import           Foreign.ForeignPtr       (ForeignPtr, withForeignPtr)
import           Foreign.Ptr              (castPtr, plusPtr)
import           Foreign.Storable         (peek, peekByteOff, poke, sizeOf)
import           GHC.ForeignPtr           (mallocPlainForeignPtrBytes)
import           Prelude                  hiding (length)

import           GHC.Base                 (realWorld#)
import           GHC.IO                   (IO (IO))

-- | Just like unsafePerformIO, but we inline it. Big performance gains as
-- it exposes lots of things to further inlining. /Very unsafe/. In
-- particular, you should do no memory allocation inside an
-- 'inlinePerformIO' block. On Hugs this is just @unsafePerformIO@.
inlinePerformIO :: IO a -> a
inlinePerformIO (IO m) = case m realWorld# of (# _, r #) -> r
{-# INLINE inlinePerformIO #-}

-- If _cap is zero, this buffer is empty.
data Buffer = Buf {
      _fp  :: {-# UNPACK #-} !(ForeignPtr Word8)
    , _off :: {-# UNPACK #-} !Int
    , _len :: {-# UNPACK #-} !Int
    , _cap :: {-# UNPACK #-} !Int
    , _gen :: {-# UNPACK #-} !Int
    }

instance Show Buffer where
    showsPrec p = showsPrec p . unbuffer

-- | The initial 'Buffer' has no mutable zone, so we can avoid all
-- copies in the (hopefully) common case of no further input being fed
-- to us.
buffer :: ByteString -> Buffer
buffer (PS fp off len) = Buf fp off len len 0
{-# INLINE buffer #-}

unbuffer :: Buffer -> ByteString
unbuffer (Buf fp off len _ _) = PS fp off len
{-# INLINE unbuffer #-}

toForeignPtr :: Buffer -> (ForeignPtr Word8, Int, Int)
toForeignPtr (Buf fp off len _ _) = (fp, off, len)
{-# INLINE toForeignPtr #-}

instance Semigroup Buffer where
    (Buf _ _ _ 0 _) <> b                    = b
    a               <> (Buf _ _ _ 0 _)      = a
    buf             <> (Buf fp off len _ _) = append buf fp off len

instance Monoid Buffer where
    mempty = Buf nullForeignPtr 0 0 0 0

    mappend = (<>)

    mconcat [] = Mon.mempty
    mconcat xs = foldl1' mappend xs

pappend :: Buffer -> ByteString -> Buffer
pappend (Buf _ _ _ 0 _) bs  = buffer bs
pappend buf (PS fp off len) = append buf fp off len
{-# INLINE pappend #-}

append :: Buffer -> ForeignPtr a -> Int -> Int -> Buffer
append (Buf fp0 off0 len0 cap0 gen0) !fp1 !off1 !len1 =
  inlinePerformIO . withForeignPtr fp0 $ \ptr0 ->
    withForeignPtr fp1 $ \ptr1 -> do
      let genSize = sizeOf (0::Int)
          newlen  = len0 + len1
      gen <- if gen0 == 0
             then return 0
             else peek (castPtr ptr0)
      if gen == gen0 && newlen <= cap0
        then do
          let newgen = gen + 1
          poke (castPtr ptr0) newgen
          memcpy (ptr0 `plusPtr` (off0+len0))
                 (ptr1 `plusPtr` off1)
                 (fromIntegral len1)
          return (Buf fp0 off0 newlen cap0 newgen)
        else do
          let newcap = newlen * 2
          fp <- mallocPlainForeignPtrBytes (newcap + genSize)
          withForeignPtr fp $ \ptr_ -> do
            let ptr    = ptr_ `plusPtr` genSize
                newgen = 1
            poke (castPtr ptr_) newgen
            memcpy ptr (ptr0 `plusPtr` off0) (fromIntegral len0)
            memcpy (ptr `plusPtr` len0) (ptr1 `plusPtr` off1)
                   (fromIntegral len1)
            return (Buf fp genSize newlen newcap newgen)

length :: Buffer -> Int
length (Buf _ _ len _ _) = len
{-# INLINE length #-}

unsafeShrink :: Int -> Int -> Buffer -> Buffer
unsafeShrink s l (Buf fp off len cap gen) =
  assert (s >= 0 && s <= len) .
  assert (l >= 0 && l <= len-s) $
  Buf fp (off+s) l cap gen
{-# INLINE unsafeShrink #-}

unsafeHead :: Buffer -> Word8
unsafeHead (Buf fp off len _ _) =
  inlinePerformIO . withForeignPtr fp $ flip peekByteOff off
{-# INLINE unsafeHead #-}

unsafeIndex :: Buffer -> Int -> Word8
unsafeIndex (Buf fp off len _ _) i = assert (i >= 0 && i < len) .
    inlinePerformIO . withForeignPtr fp $ flip peekByteOff (off+i)
{-# INLINE unsafeIndex #-}

unsafeSubstring :: Int -> Int -> Buffer -> ByteString
unsafeSubstring s l (Buf fp off len _ _) =
  assert (s >= 0 && s <= len) .
  assert (l >= 0 && l <= len-s) $
  PS fp (off+s) l
{-# INLINE unsafeSubstring #-}

unsafeDrop :: Int -> Buffer -> ByteString
unsafeDrop s (Buf fp off len _ _) =
  assert (s >= 0 && s <= len) $
  PS fp (off+s) (len-s)
{-# INLINE unsafeDrop #-}

substring :: Int -> Int -> Buffer -> ByteString
substring s l (Buf fp off len _ _)
  | s >= 0 && s <= len &&
    l >= 0 && l <= len-s = PS fp (off+s) l
  | otherwise = mempty
