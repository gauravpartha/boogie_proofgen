@echo off
setlocal

set BGEXE=..\..\Binaries\Boogie.exe

for %%f in (foo.bpl bar.bpl one.bpl parallel1.bpl) do (
  echo.
  echo -------------------- %%f --------------------
  %BGEXE% %* /nologo /noinfer %%f
)

for %%f in (linear-set.bpl linear-set2.bpl FlanaganQadeer.bpl parallel2.bpl parallel4.bpl parallel5.bpl akash.bpl t1.bpl new1.bpl perm.bpl DeviceCache.bpl ticket.bpl lock.bpl lock2.bpl multiset.bpl civl-paper.bpl) do (
  echo.
  echo -------------------- %%f --------------------
  %BGEXE% %* /nologo /noinfer /typeEncoding:m /useArrayTheory %%f
)

