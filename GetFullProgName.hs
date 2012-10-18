{-# LANGUAGE ForeignFunctionInterface #-}
module GetFullProgName (getFullProgName) where

import Foreign
import Foreign.C

getFullProgName :: IO String
getFullProgName =
  alloca $ \ p_argc ->
  alloca $ \ p_argv -> do
   getFullProgArgv p_argc p_argv
   peek p_argv >>= peek >>= peekCString

foreign import ccall unsafe "getFullProgArgv"
    getFullProgArgv :: Ptr CInt -> Ptr (Ptr CString) -> IO ()

