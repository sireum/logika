::#! 2> /dev/null                                                                                           #
@ 2>/dev/null # 2>nul & echo off & goto BOF                                                                 #
export SIREUM_HOME=$(cd -P $(dirname "$0")/.. && pwd -P)                                                    #
if [ ! -z ${SIREUM_PROVIDED_SCALA++} ]; then                                                                #
  SIREUM_PROVIDED_JAVA=true                                                                                 #
fi                                                                                                          #
"${SIREUM_HOME}/bin/init.sh"                                                                                #
if [ -n "$COMSPEC" -a -x "$COMSPEC" ]; then                                                                 #
  export SIREUM_HOME=$(cygpath -C OEM -w -a ${SIREUM_HOME})                                                 #
  if [ -z ${SIREUM_PROVIDED_JAVA++} ]; then                                                                 #
    export PATH="${SIREUM_HOME}/bin/win/java":"${SIREUM_HOME}/bin/win/z3":"$PATH"                           #
    export PATH="$(cygpath -C OEM -w -a ${JAVA_HOME}/bin)":"$(cygpath -C OEM -w -a ${Z3_HOME}/bin)":"$PATH" #
  fi                                                                                                        #
elif [ "$(uname)" = "Darwin" ]; then                                                                        #
  if [ -z ${SIREUM_PROVIDED_JAVA++} ]; then                                                                 #
    export PATH="${SIREUM_HOME}/bin/mac/java/bin":"${SIREUM_HOME}/bin/mac/z3/bin":"$PATH"                   #
  fi                                                                                                        #
elif [ "$(expr substr $(uname -s) 1 5)" = "Linux" ]; then                                                   #
  if [ -z ${SIREUM_PROVIDED_JAVA++} ]; then                                                                 #
    if [ "$(uname -m)" = "aarch64" ]; then                                                                  #
      export PATH="${SIREUM_HOME}/bin/linux/arm/java/bin":"$PATH"                                           #
    else                                                                                                    #
      export PATH="${SIREUM_HOME}/bin/linux/java/bin":"${SIREUM_HOME}/bin/linux/z3/bin":"$PATH"             #
    fi                                                                                                      #
  fi                                                                                                        #
fi                                                                                                          #
if [ -f "$0.com" ] && [ "$0.com" -nt "$0" ]; then                                                           #
  exec "$0.com" "$@"                                                                                        #
else                                                                                                        #
  rm -fR "$0.com"                                                                                           #
  exec "${SIREUM_HOME}/bin/sireum" slang run -n "$0" "$@"                                                #
fi                                                                                                          #
:BOF
setlocal
set SIREUM_HOME=%~dp0../
call "%~dp0init.bat"
if defined SIREUM_PROVIDED_SCALA set SIREUM_PROVIDED_JAVA=true
if not defined SIREUM_PROVIDED_JAVA set PATH=%~dp0win\java\bin;%~dp0win\z3\bin;%PATH%
set NEWER=False
if exist %~dpnx0.com for /f %%i in ('powershell -noprofile -executionpolicy bypass -command "(Get-Item %~dpnx0.com).LastWriteTime -gt (Get-Item %~dpnx0).LastWriteTime"') do @set NEWER=%%i
if "%NEWER%" == "True" goto native
del "%~dpnx0.com" > nul 2>&1
"%~dp0sireum.bat" slang run -n "%0" %*
exit /B %errorlevel%
:native
%~dpnx0.com %*
exit /B %errorlevel%
::!#
// #Sireum
import org.sireum._


def usage(): Unit = {
  println("Sireum Logika /build")
  println("Usage: ( compile | test | test-js )+")
}


if (Os.cliArgs.isEmpty) {
  usage()
  Os.exit(0)
}


val homeBin = Os.slashDir
val home = homeBin.up
val sireumJar = homeBin / "sireum.jar"
val mill = homeBin / "mill.bat"
var didTipe = F
var didCompile = F
val versions = (home / "versions.properties").properties
val cache = Os.home / "Downloads" / "sireum"


def platformKind(kind: Os.Kind.Type): String = {
  kind match {
    case Os.Kind.Win => return "win"
    case Os.Kind.Linux => return "linux"
    case Os.Kind.LinuxArm => return "linux/arm"
    case Os.Kind.Mac => return "mac"
    case _ => return "unsupported"
  }
}


def downloadMill(): Unit = {
  if (!mill.exists) {
    println("Downloading mill ...")
    mill.downloadFrom("https://github.com/sireum/rolling/releases/download/mill/standalone")
    mill.chmod("+x")
    println()
  }
}


def installZ3(kind: Os.Kind.Type): Unit = {
  val version = versions.get("org.sireum.version.z3").get
  val dir = homeBin / platformKind(kind) / "z3"
  val ver = dir / "VER"

  if (ver.exists && ver.read == version) {
    return
  }

  val filename: String = kind match {
    case Os.Kind.Win => s"z3-$version-x64-win.zip"
    case Os.Kind.Linux => s"z3-$version-x64-glibc-2.31.zip"
    case Os.Kind.Mac =>
      if (ops.StringOps(proc"uname -m".run().out).trim == "arm64") s"z3-$version-arm64-osx-11.0.zip"
      else s"z3-$version-x64-osx-10.16.zip"
    case _ => return
  }

  val bundle = cache / filename

  if (!bundle.exists) {
    println(s"Please wait while downloading Z3 $version ...")
    bundle.up.mkdirAll()
    bundle.downloadFrom(s"https://github.com/Z3Prover/z3/releases/download/z3-$version/$filename")
    println()
  }

  println("Extracting Z3 ...")
  bundle.unzipTo(dir.up)

  for (p <- dir.up.list if ops.StringOps(p.name).startsWith("z3-")) {
    dir.removeAll()
    p.moveTo(dir)
  }

  kind match {
    case Os.Kind.Linux => (dir / "bin" / "z3").chmod("+x")
    case Os.Kind.Mac => (dir / "bin" / "z3").chmod("+x")
    case _ =>
  }

  ver.writeOver(version)
}


def installCVC(kind: Os.Kind.Type): Unit = {
  def installCVCGen(gen: String, version: String): Unit = {
    val genOpt: Option[String] = if (gen == "4") None() else Some(gen)
    val exe = homeBin / platformKind(kind) / (if (kind == Os.Kind.Win) st"cvc$genOpt.exe" else st"cvc$genOpt").render
    val ver = homeBin / platformKind(kind) / st".cvc$genOpt.ver".render

    val VER = s"$gen-$version"

    if (ver.exists && ver.read == VER) {
      return
    }

    val (sub, filename, dropname): (String, String, String) = (gen, kind) match {
      case (string"5", Os.Kind.Win) => (s"cvc$gen-$version", s"cvc$gen-Win64.exe", s"cvc$gen-$version-Win64.exe")
      case (string"5", Os.Kind.Linux) => (s"cvc$gen-$version", s"cvc$gen-Linux", s"cvc$gen-$version-Linux")
      case (string"5", Os.Kind.Mac) =>
        if (ops.StringOps(proc"uname -m".run().out).trim == "arm64")
          (s"cvc$gen-$version", s"cvc$gen-macOS-arm64", s"cvc$gen-$version-macOS-arm64")
        else (s"cvc$gen-$version", s"cvc$gen-macOS", s"cvc$gen-$version-macOS")
      case (string"4", Os.Kind.Win) => (version, s"cvc$gen-$version-win64-opt.exe", s"cvc$gen-$version-win64-opt.exe")
      case (string"4", Os.Kind.Linux) => (version, s"cvc$gen-$version-x86_64-linux-opt", s"cvc$gen-$version-x86_64-linux-opt")
      case (string"4", Os.Kind.Mac) => (version, s"cvc$gen-$version-macos-opt", s"cvc$gen-$version-macos-opt")
      case _ => return
    }

    val drop = cache / dropname

    if (!drop.exists) {
      println(s"Please wait while downloading CVC$gen $version ...")
      drop.up.mkdirAll()
      drop.downloadFrom(s"https://github.com/cvc5/cvc5/releases/download/$sub/$filename")
      println()
    }

    drop.copyOverTo(exe)

    kind match {
      case Os.Kind.Linux => exe.chmod("+x")
      case Os.Kind.Mac => exe.chmod("+x")
      case _ =>
    }

    ver.writeOver(VER)
    println()
  }
  val (gen1, genVersion1, gen2, genVersion2): (String, String, String, String) =
    ops.StringOps(versions.get("org.sireum.version.cvc").get).split((c: C) => c == '-' || c == ',') match {
      case ISZ(g1, gv1, g2, gv2) => (g1, gv1, g2, gv2)
      case ISZ(string"1.8") => ("4", "1.8", "4", "1.8")
      case ISZ(version) => ("5", version, "5", version)
    }
  installCVCGen(gen1, genVersion1)
  if (gen1 != gen2) {
    installCVCGen(gen2, genVersion2)
  }
}


def installAltErgoOpen(kind: Os.Kind.Type): Unit = {
  val version = versions.get("org.sireum.version.alt-ergo-open").get
  val dir = homeBin / platformKind(kind)
  val exe = dir / "alt-ergo-open"
  val ver = dir / ".alt-ergo-open.ver"

  if (ver.exists && ver.read == version) {
    return
  }

  val filename: String = kind match {
    case Os.Kind.Linux => s"alt-ergo-open-$version-linux"
    case Os.Kind.Mac => s"alt-ergo-open-$version-mac"
    case _ => return
  }

  val drop = cache / filename

  if (!drop.exists) {
    println(s"Please wait while downloading Alt-Ergo $version (Apache 2.0 Licence) ...")
    drop.up.mkdirAll()
    drop.downloadFrom(s"https://github.com/sireum/rolling/releases/download/alt-ergo-open/$filename")
    println()
  }

  drop.copyOverTo(exe)

  exe.chmod("+x")

  ver.writeOver(version)
}


def clone(repo: String): Unit = {
  if (!(home / repo).exists) {
    Os.proc(ISZ("git", "clone", "--depth=1", s"https://github.com/sireum/$repo")).at(home).console.runCheck()
  } else {
    Os.proc(ISZ("git", "pull")).at(home / repo).console.runCheck()
  }
  val currBranch = ops.StringOps(proc"git rev-parse --abbrev-ref HEAD".at(home).runCheck().out).trim
  val branchExistsInRepo = ops.StringOps(proc"git ls-remote --heads origin ${currBranch}".at(home / repo).run().out).trim.size > 0
  if(branchExistsInRepo) {
    proc"git remote set-branches origin $currBranch".at(home / repo).runCheck()
    proc"git fetch".at(home / repo).runCheck()
    proc"git checkout $currBranch".at(home / repo).runCheck()
  }

  println()
}


def tipe(): Unit = {
  if (!didTipe) {
    didTipe = T
    println("Slang type checking ...")
    Os.proc(ISZ("java", "-jar", sireumJar.string, "slang", "tipe", "--verbose", "-r", "-s", home.string)).
      at(home).console.runCheck()
    println()
  }
}


def compile(): Unit = {
  if (!didCompile) {
    didCompile = T
    tipe()
    println("Compiling ...")
    Os.proc(ISZ(mill.string, "all", "logika.shared.tests.compile")).at(home).console.runCheck()
    println()
  }
}


def test(): Unit = {
  compile()
  println("Running shared tests ...")
  Os.proc(ISZ(mill.string, "logika.jvm.tests")).at(home).console.runCheck()
  println()
}


def testJs(): Unit = {
  compile()
  println("Running js tests ...")
  Os.proc(ISZ(mill.string, "logika.js.tests")).at(home).console.runCheck()
  println()
}


downloadMill()
installZ3(Os.kind)
installCVC(Os.kind)
installAltErgoOpen(Os.kind)

for (m <- ISZ("runtime", "slang")) {
  clone(m)
}

for (i <- 0 until Os.cliArgs.size) {
  Os.cliArgs(i) match {
    case string"compile" => compile()
    case string"test" => test()
    case string"test-js" => testJs()
    case cmd =>
      usage()
      eprintln(s"Unrecognized command: $cmd")
      Os.exit(-1)
  }
}