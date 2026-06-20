$m = [Environment]::GetEnvironmentVariable('PATH','Machine')
if ($m -notlike '*C:\LLVM\bin*') {
  [Environment]::SetEnvironmentVariable('PATH', 'C:\LLVM\bin;' + $m, 'Machine')
  'ADDED'
} else { 'ALREADY' }
