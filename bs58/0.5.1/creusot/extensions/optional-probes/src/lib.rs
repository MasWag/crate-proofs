use creusot_std::prelude::*;
pub fn small_resize(v: &mut smallvec::SmallVec<[u8; 32]>, n: usize) { v.resize(n, 0); }
pub fn small_truncate(v: &mut smallvec::SmallVec<[u8; 32]>, n: usize) { v.truncate(n); }
pub fn small_slice(v: &mut smallvec::SmallVec<[u8; 32]>) -> &mut [u8] { &mut v[..] }
pub fn array_spare(v: &mut tinyvec::ArrayVec<[u8; 32]>) -> &mut [u8] { v.grab_spare_slice_mut() }
pub fn array_set_len(v: &mut tinyvec::ArrayVec<[u8; 32]>, n: usize) { v.set_len(n); }
pub fn slice_spare<'a, 'b>(v: &'a mut tinyvec::SliceVec<'b, u8>) -> &'a mut [u8] { v.grab_spare_slice_mut() }
pub fn slice_set_len(v: &mut tinyvec::SliceVec<'_, u8>, n: usize) { v.set_len(n); }
pub fn tiny_resize(v: &mut tinyvec::TinyVec<[u8; 32]>, n: usize) { v.resize(n, 0); }
pub fn tiny_truncate(v: &mut tinyvec::TinyVec<[u8; 32]>, n: usize) { v.truncate(n); }
pub fn tiny_slice(v: &mut tinyvec::TinyVec<[u8; 32]>) -> &mut [u8] { &mut v[..] }
