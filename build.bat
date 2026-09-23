@echo off
REM Build script for the C-HD project (MSVC, x64).
REM Usage: build.bat [Debug^|Release] [target]
REM   targets: lib (default), tests, bench, all
setlocal enabledelayedexpansion
set CONF=%1
if "%CONF%"=="" set CONF=Release
set TARGET=%2
if "%TARGET%"=="" set TARGET=all

call "C:\Program Files\Microsoft Visual Studio\2022\Community\VC\Auxiliary\Build\vcvars64.bat" >nul
if errorlevel 1 (
  echo [build] vcvars64 not found - is VS2022 Community installed?
  exit /b 1
)

set CFLAGS=/nologo /std:c17 /W3 /wd4244 /wd4267 /I include /fp:precise /GS- /DNDEBUG
if "%CONF%"=="Debug" (set CFLAGS=/nologo /std:c17 /W3 /wd4244 /wd4267 /I include /Od /Zi /RTC1 /DCHD_DEBUG) else (set CFLAGS=%CFLAGS% /O2 /Ob3)

if not exist build mkdir build
if not exist build\%CONF% mkdir build\%CONF%

echo [build] config=%CONF% target=%TARGET%
echo [build] cl %CFLAGS%

set OBJS=
for %%S in (src\common.c src\dijkstra.c src\bellman_ford.c src\chd.c) do (
  set OBJ=build\%CONF%\%%~nS.obj
  cl %CFLAGS% /c %%S /Fo!OBJ! || exit /b 1
  set OBJS=!OBJS! !OBJ!
)

if "%TARGET%"=="lib" goto :eof

if "%TARGET%"=="tests" goto :tests
if "%TARGET%"=="bench"  goto :bench
if "%TARGET%"=="all" goto :tests

:tests
cl %CFLAGS% tests\test_chd.c %OBJS% /Fe:build\%CONF%\test_chd.exe || exit /b 1
echo [build] build\%CONF%\test_chd.exe
if "%TARGET%"=="tests" goto :eof

:bench
set DOBJS=
for %%S in (dmmsy\dmmsy_common.c dmmsy\dmmsy_opt.c) do (
  set OBJ=build\%CONF%\%%~nS.obj
  cl %CFLAGS% /c %%S /Fo!OBJ! || exit /b 1
  set DOBJS=!DOBJS! !OBJ!
)
cl %CFLAGS% src\benchmark.c %OBJS% %DOBJS% /Fe:build\%CONF%\chd_bench.exe || exit /b 1
echo [build] build\%CONF%\chd_bench.exe
if "%TARGET%"=="all" goto :eof
