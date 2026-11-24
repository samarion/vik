val scala3Version = "3.10.1"

// In sbt 2, bare settings are common settings injected into all subprojects.
organization := "io.bovel"

// Publishing to Maven Central (through the Sonatype Central Portal): the version comes from the git
// tag (sbt-dynver: pushing `v0.1.0` publishes 0.1.0), signing and upload are sbt-ci-release in the
// `publish` job of the CI — see "Releasing" in CONTRIBUTING.md.
homepage := Some(uri("https://github.com/mbovel/vik"))
licenses := List(License.Apache2)
developers := List(Developer("mbovel", "Matthieu Bovel", "matthieu@bovel.net", uri("https://github.com/mbovel")))
scmInfo := Some(ScmInfo(uri("https://github.com/mbovel/vik"), "scm:git:git@github.com:mbovel/vik.git"))
versionScheme := Some("early-semver")

// Every JVM test suite runs forked with the same fixed heap on every machine, so the sbt server
// only builds: without this, all modules' tests share the server heap and its classloader caches,
// which exhausted CI's three gigabytes (HoCoreTest OOMed after the earlier suites filled it).
// The solver's Scala Native binary in release mode: Scala Native links in `debug` mode unless told otherwise
// (no optimizer, no link-time optimization), which is what the evaluation measured until 2026-09-03 — release
// with thin LTO is 3–5× faster where the search takes time (`bench/results/smt/2026-09-03-laraserver4-native-release.md`).
// Only the `vik` row's main binary gets it, the one cold.sh measures; the test binaries stay quick to link.
// VIK_NATIVE_FLAGS adds options to the C/C++ compilation and the link, for a toolchain that needs them
// (laraserver4's user-space LLVM: `-stdlib=libc++ -fuse-ld=lld -Wl,-rpath,<its lib/x86_64-unknown-linux-gnu>`).
import scala.scalanative.build.{GC, LTO, Mode}
val nativeFlags = sys.env.get("VIK_NATIVE_FLAGS").toSeq.flatMap(_.split(" ")).filter(_.nonEmpty)
val nativeRelease = Seq(
  Compile / nativeConfig ~= { config =>
    config.withMode(Mode.releaseFull).withLTO(LTO.thin)
      .withCompileOptions(config.compileOptions ++ nativeFlags)
      .withLinkingOptions(config.linkingOptions ++ nativeFlags)
  },
  // The test binary follows the main one's configuration: back to debug, and the flags alone.
  Test / nativeConfig ~= { config =>
    config.withMode(Mode.debug).withLTO(LTO.none)
      .withCompileOptions(config.compileOptions ++ nativeFlags)
      .withLinkingOptions(config.linkingOptions ++ nativeFlags)
  }
)

/** The test binaries of Scala Native, single-threaded: they run their suites
 *  one after another and use no thread of their own, and the multithreaded
 *  runtime is what the intermittent `Unhandled signal 11` of the CI needs
 *  (external-issues.md: one crash in 25 runs of a deterministic suite with it,
 *  none in 28 without).
 */
val nativeTests = Seq(Test / nativeConfig ~= (_.withGC(GC.commix)))

val forkedTests = Seq(
  Test / fork := true,
  Test / javaOptions += "-Xmx2g",
  // The corpus test's wall-clock guard, when the environment raises it (CI: a hard limit, not the budget).
  Test / javaOptions ++= sys.env.get("VIK_CORPUS_BUDGET_MS").map(ms => s"-Dvik.corpus.budgetMs=$ms").toSeq
)
scalaVersion := scala3Version
scalacOptions += "-Yexplicit-nulls"

// sbt 2 caches task results on disk by their inputs and replays them. The tests and the Scala Native links are
// opted out (sbt 2.1): a replayed test run reports `Total 0` for nothing run (external-issues.md, 5 and 10), and
// a replayed `nativeLink` kept a binary whose options had changed (15). Compilation stays cached.
Test / test / cacheStores := Nil // `testOnly`, `testQuick` and `testSelected` follow `test`
nativeLink / cacheStores := Nil
// One forked JVM per module, its suites in sequence, as in sbt 2.0: sbt 2.1 splits them over two workers by
// default, each with the heap above, and the corpus suite's wall-clock guard assumes the machine to itself.
Test / testTopology := TestTopology.subprojectExclusive

// Generates the subprojects `egraph` (JVM) and `egraphJS` from the same sources.
lazy val egraph = projectMatrix
  .in(file("egraph"))
  .settings(
    name := "egraph",
    description := "A congruence closure engine with explanations (an e-graph)",
    libraryDependencies += "org.scalameta" %% "munit" % "1.3.6" % Test
  )
  .jvmPlatform(scalaVersions = Seq(scala3Version), settings = forkedTests)
  .jsPlatform(scalaVersions = Seq(scala3Version))
  .nativePlatform(scalaVersions = Seq(scala3Version), settings = nativeTests)

// Generates the subprojects `cdclt` (JVM) and `cdcltJS` from the same sources.
lazy val cdclt = projectMatrix
  .in(file("cdclt"))
  .settings(
    name := "cdclt",
    description := "A CDCL(T) SAT solver: watched literals, first-UIP learning, theories",
    libraryDependencies += "org.scalameta" %% "munit" % "1.3.6" % Test
  )
  .jvmPlatform(scalaVersions = Seq(scala3Version), settings = forkedTests)
  .jsPlatform(scalaVersions = Seq(scala3Version))
  .nativePlatform(scalaVersions = Seq(scala3Version), settings = nativeTests)

// Linear integer arithmetic (simplex and branch and bound): subprojects `lia` (JVM) and `liaJS`.
lazy val lia = projectMatrix
  .in(file("lia"))
  .settings(
    name := "lia",
    description := "Linear integer arithmetic: simplex, branch and bound in a small-model box",
    libraryDependencies += "org.scalameta" %% "munit" % "1.3.6" % Test
  )
  .jvmPlatform(scalaVersions = Seq(scala3Version), settings = forkedTests)
  .jsPlatform(scalaVersions = Seq(scala3Version))
  .nativePlatform(scalaVersions = Seq(scala3Version), settings = nativeTests)

// Terms, formulas and the solver over the theories: subprojects `vik` (JVM), `vikJS` and `vikNative`.
lazy val vik = projectMatrix
  .in(file("vik"))
  .dependsOn(cdclt, egraph, lia, smtlib)
  .settings(
    name := "vik",
    description := "A minimal, readable SMT solver",
    Compile / mainClass := Some("io.bovel.vik.run"), // the command line, also as a native binary
    libraryDependencies += "org.scalameta" %% "munit" % "1.3.6" % Test
  )
  .jvmPlatform(scalaVersions = Seq(scala3Version), settings = forkedTests)
  .jsPlatform(scalaVersions = Seq(scala3Version))
  .nativePlatform(scalaVersions = Seq(scala3Version), settings = nativeRelease ++ nativeTests)

// SMT-LIB 2 scripts: subprojects `smtlib` (JVM) and `smt2JS`.
lazy val smtlib = projectMatrix
  .in(file("smtlib"))
  .settings(
    name := "smtlib",
    description := "SMT-LIB 2 as written: trees, parser, printer",
    libraryDependencies += "org.scalameta" %% "munit" % "1.3.6" % Test
  )
  .jvmPlatform(scalaVersions = Seq(scala3Version), settings = forkedTests)
  .jsPlatform(scalaVersions = Seq(scala3Version))
  .nativePlatform(scalaVersions = Seq(scala3Version), settings = nativeTests)

lazy val runtimeClasspath = taskKey[String]("The runtime classpath, colon-separated, as real paths")

lazy val vikJVM = vik.jvm(scala3Version)
  .settings(
    // The runtime classpath as real paths, for the tools that run the solver's `smt2` outside sbt (cold.sh, aot.sh).
    runtimeClasspath := {
      val converter = fileConverter.value
      (Runtime / fullClasspath).value.map(entry => converter.toPath(entry.data).toString).mkString(":")
    }
  )

// The solver as a GraalVM native image (bench/graal.sh: `graal/nativeImageCopy target/graal/vik`), a binary that
// answers in milliseconds where the JVM takes a third of a second (the evaluation's cold table). A project of its
// own, without sources: the plugin adds a dependency (svm-subs) that the published `vik` must not carry. The plugin
// fetches GraalVM (graalvm-java25) through coursier unless NATIVE_IMAGE_INSTALLED=true names one in GRAALVM_HOME;
// --no-fallback: a binary, or a failure.
lazy val graal = project
  .in(file("graal"))
  .enablePlugins(NativeImagePlugin)
  .dependsOn(ClasspathDependency(vikJVM, None) +: jvmSuites.map(p => ClasspathDependency(p, Some("test->test"))) *)
  .settings(
    name := "graal",
    publish / skip := true,
    Compile / mainClass := Some("io.bovel.vik.run"),
    // Every suite the JVM runs, in a native image of their own (`graal/nativeImageTest`, then
    // `graal/nativeImageTestRun`): what the binary answers, not only that it starts. The image carries no
    // test framework, so `Suites.scala` is generated from what sbt discovers and the runner walks it.
    Test / mainClass := Some("io.bovel.vik.graal.TestMain"),
    Test / sourceGenerators += Def.taskDyn {
      val out = (Test / sourceManaged).value / "Suites.scala"
      val discovered = Def.task {
        (jvmSuites.map(p => (p / Test / definedTests)).join.value.flatten.map(_.name)).distinct.sorted
      }
      Def.task {
        val names = discovered.value
        IO.write(
          out,
          s"""package io.bovel.vik.graal
             |
             |/** Every suite sbt discovers in the modules the image carries, generated by the build
             |  * (`graal / Test / sourceGenerators`): the image has no test framework to find them, and a
             |  * list written by hand would fall behind the suites.
             |  */
             |object Suites:
             |  def all: List[munit.Suite] = List(
             |${names.map(n => s"    $n()").mkString(",\n")}
             |  )
             |""".stripMargin
        )
        Seq(out)
      }
    }.taskValue,
    libraryDependencies += "org.scalameta" %% "munit" % "1.3.6" % Test,
    nativeImageOptions ++= Seq("--no-fallback", "-O2")
  )

/** The JVM projects whose suites the native image of the tests carries. */
lazy val jvmSuites = Seq[ProjectReference](
  egraph.jvm(scala3Version),
  cdclt.jvm(scala3Version),
  lia.jvm(scala3Version),
  smtlib.jvm(scala3Version),
  vikJVM,
  smtlibutils
)

// The corpus on disk and its importer, and the tests that play it (JVM only): forked with a fixed
// heap, the same memory budget on every machine.
lazy val smtlibutils = (project in file("smtlibutils"))
  .dependsOn(vikJVM, vikJVM % "test->test")
  .settings(
    name := "smtlibutils",
    publish / skip := true, // corpus tooling and tests, not a library
    libraryDependencies += "org.scalameta" %% "munit" % "1.3.6" % Test,
    // The tools run in a JVM of their own, from the repository's root like the unforked ones: `ignorestamp`
    // runs four files at a time, each used to the tests' 2 GB.
    run / fork := true,
    run / baseDirectory := (ThisBuild / baseDirectory).value,
    run / javaOptions += "-Xmx8g"
  )
  .settings(forkedTests *)

// What consumes Vik's proofs (JVM only): the driver that writes a certificate as Lean files for `proofs/lean`
// to check, and the tool that writes those of a corpus (`proofs/runMain io.bovel.vik.proofs.LeanCorpus`).
lazy val proofs = (project in file("proofs"))
  .dependsOn(vikJVM)
  .settings(
    name := "proofs",
    publish / skip := true,
    libraryDependencies += "org.scalameta" %% "munit" % "1.3.6" % Test,
    run / fork := true,
    run / baseDirectory := (ThisBuild / baseDirectory).value,
    run / javaOptions += "-Xmx8g"
  )
  .settings(forkedTests *)

// The browser playgrounds (Scala.js): the e-graph and the SMT-LIB front end.
import org.scalajs.linker.interface.ESVersion

// The solver as a WebAssembly module for the runnable snippets of the documentation (see the `site` task).
lazy val docsPlayground = project
  .in(file("docsPlayground"))
  .enablePlugins(ScalaJSPlugin)
  .dependsOn(vik.js(scala3Version))
  .settings(
    name := "docsPlayground",
    publish / skip := true,
    scalaJSLinkerConfig ~= {
      _.withESFeatures(_.withUseWebAssembly(true).withESVersion(ESVersion.ES2022)).withModuleKind(ModuleKind.ESModule)
    }
  )

// The same module, on the JavaScript backend, for the engines that have no Wasm 3.0 (Safari before 26).
lazy val docsPlaygroundJs = project
  .in(file("target/docsPlayground-js"))
  .enablePlugins(ScalaJSPlugin)
  .dependsOn(vik.js(scala3Version))
  .settings(
    name := "docsPlaygroundJs",
    publish / skip := true,
    Compile / scalaSource := (docsPlayground / Compile / scalaSource).value,
    scalaJSLinkerConfig ~= { _.withModuleKind(ModuleKind.ESModule) }
  )

lazy val playground = project
  .in(file("playground"))
  .enablePlugins(ScalaJSPlugin)
  .dependsOn(egraph.js(scala3Version), vik.js(scala3Version))
  .settings(
    name := "playground",
    publish / skip := true,
    scalaJSUseMainModuleInitializer := true,
    // WebAssembly too (see the JS rows below): the pages load `main.js` as an ES module, which fetches `main.wasm`.
    scalaJSLinkerConfig ~= {
      _.withESFeatures(_.withUseWebAssembly(true).withESVersion(ESVersion.ES2022)).withModuleKind(ModuleKind.ESModule)
    },
    libraryDependencies += "org.scala-js" %% "scalajs-dom" % "2.8.1"
  )

// The runtime classpath of a project as real paths, for scripts (sbt 2 exports virtual file references).
// JMH benchmarks of every module (JVM only), and the comparison with other solvers: `sbt "bench/Jmh/run"`.
lazy val bench = project
  .in(file("bench"))
  .enablePlugins(JmhPlugin)
  .dependsOn(
    smtlibutils,
    egraph.jvm(scala3Version),
    cdclt.jvm(scala3Version),
    lia.jvm(scala3Version),
    vik.jvm(scala3Version),
    smtlib.jvm(scala3Version)
  )
  .settings(
    name := "bench",
    publish / skip := true,
    // Other solvers, run in-process by the benchmarks and as separate processes by compare.sh.
    libraryDependencies ++= Seq(
      ("io.github.uuverifiers" %% "princess" % "2026-05-20").cross(CrossVersion.for3Use2_13),
      "de.uni-freiburg.informatik.ultimate" % "smtinterpol" % "2.5-1388-ga5a4ab0c",
      // The Java bindings of z3 and cvc5 as published by SoSy-Lab (JavaSMT); their native libraries come from
      // bench/fetch-native.sh into bench/native, found through java.library.path below. The cvc5 one is a
      // snapshot of cvc5's main taken the day after the 1.3.3 tag (four housekeeping commits past it): SoSy-Lab
      // stopped publishing release builds after 1.2.1, whose binding scans a list of every object created for
      // each new term (external-issues.md).
      "org.sosy-lab" % "javasmt-solver-z3" % "4.14.0",
      "org.sosy-lab" % "javasmt-solver-cvc5" % "2026-02-26-d22638a"
    ),
    // Scala 3.10.1 warns on `catch case _: Throwable` (E235). The harness catches it on purpose: a replay's
    // StackOverflowError or AssertionError is a result to report, not a reason to stop.
    scalacOptions += "-Wconf:id=E235:s",
    fork := true, // runs and benchmarks in their own JVM, with the native libraries of z3 and cvc5 on its path
    // The Java that sbt-jmh generates is compiled for 17 whatever JDK runs the build: a class compiled by a
    // newer one stays in target/ and a build on 17 then cannot load it (UnsupportedClassVersionError).
    javacOptions ++= Seq("--release", "17"),
    javaOptions += s"-Djava.library.path=${baseDirectory.value / "native"}",
    Jmh / run / javaOptions += s"-Djava.library.path=${baseDirectory.value / "native"}",
    runtimeClasspath := {
      val converter = fileConverter.value
      (Runtime / fullClasspath).value.map(entry => converter.toPath(entry.data).toString).mkString(":")
    }
  )

// Scala.js on the WebAssembly backend: ES modules and ES 2022 are required.
lazy val egraphJS = egraph.js(scala3Version)
lazy val cdcltJS = cdclt.js(scala3Version)
lazy val liaJS = lia.js(scala3Version)
lazy val vikJS = vik.js(scala3Version)
lazy val smt2JS = smtlib.js(scala3Version)
egraphJS / scalaJSLinkerConfig ~=
  { _.withESFeatures(_.withUseWebAssembly(true).withESVersion(ESVersion.ES2022)).withModuleKind(ModuleKind.ESModule) }
cdcltJS / scalaJSLinkerConfig ~=
  { _.withESFeatures(_.withUseWebAssembly(true).withESVersion(ESVersion.ES2022)).withModuleKind(ModuleKind.ESModule) }
liaJS / scalaJSLinkerConfig ~=
  { _.withESFeatures(_.withUseWebAssembly(true).withESVersion(ESVersion.ES2022)).withModuleKind(ModuleKind.ESModule) }
vikJS / scalaJSLinkerConfig ~=
  { _.withESFeatures(_.withUseWebAssembly(true).withESVersion(ESVersion.ES2022)).withModuleKind(ModuleKind.ESModule) }
smt2JS / scalaJSLinkerConfig ~=
  { _.withESFeatures(_.withUseWebAssembly(true).withESVersion(ESVersion.ES2022)).withModuleKind(ModuleKind.ESModule) }

// Scala Native: the same sources again, with a `Native` suffix (clang: on the path, or `LLVM_BIN`).

// The API documentation of the six modules (their JVM rows) as one site: `sbt unidoc`, in `target/unidoc`.
lazy val docsAssets = taskKey[Unit]("The solver as a WebAssembly module for the runnable snippets of the site")

// The documentation site: the solver linked for the snippets, then the pages of `docs/` and the API documentation.
addCommandAlias("site", "docsAssets; unidoc")

// The test suites by platform, one CI job each: the six modules on the JVM with the corpus, then the same six on
// Scala.js (Node.js, the WebAssembly backend) and on Scala Native (clang). `sbt test` at the root is the JVM rows.
addCommandAlias(
  "testJVM",
  "egraph/test; cdclt/test; lia/test; vik/test; smtlib/test; smtlibutils/test; proofs/test"
)
addCommandAlias("testJS", "egraphJS/test; cdcltJS/test; liaJS/test; vikJS/test; smtlibJS/test")
addCommandAlias(
  "testNative",
  "egraphNative/test; cdcltNative/test; liaNative/test; vikNative/test; smtlibNative/test"
)

// The same three, compiled and not run: the CI compiles in one step and runs in the next, so a red job
// says which of the two it was, and how long each took.
addCommandAlias(
  "compileJVM",
  "egraph/Test/compile; cdclt/Test/compile; lia/Test/compile; vik/Test/compile; smtlib/Test/compile; " +
    "smtlibutils/Test/compile; proofs/Test/compile"
)
addCommandAlias(
  "compileJS",
  "egraphJS/Test/compile; cdcltJS/Test/compile; liaJS/Test/compile; vikJS/Test/compile; smtlibJS/Test/compile"
)
addCommandAlias(
  "compileNative",
  "egraphNative/Test/compile; cdcltNative/Test/compile; liaNative/Test/compile; vikNative/Test/compile; " +
    "smtlibNative/Test/compile"
)

// Formatting, every project: the root aggregates the five modules' JVM rows only (their JS and Native rows share
// the sources), so the projects outside it are named. `formatCheckAll` is CI's format job.
addCommandAlias(
  "formatAll",
  "scalafmtAll; scalafmtSbt; bench/scalafmtAll; smtlibutils/scalafmtAll; proofs/scalafmtAll; playground/scalafmtAll; " +
    "docsPlayground/scalafmtAll; graal/scalafmtAll"
)
addCommandAlias(
  "formatCheckAll",
  "scalafmtCheckAll; scalafmtSbtCheck; bench/scalafmtCheckAll; smtlibutils/scalafmtCheckAll; proofs/scalafmtCheckAll; " +
    "playground/scalafmtCheckAll; docsPlayground/scalafmtCheckAll; graal/scalafmtCheckAll"
)

lazy val root = (project in file("."))
  .enablePlugins(ScalaUnidocPlugin)
  .aggregate(
    egraph.jvm(scala3Version),
    cdclt.jvm(scala3Version),
    lia.jvm(scala3Version),
    vik.jvm(scala3Version),
    smtlib.jvm(scala3Version)
  )
  .settings(
    name := "vik-root", // the aggregate; the solver module is `vik`
    publish / skip := true,
    ScalaUnidoc / unidoc / unidocProjectFilter := inProjects(
      egraph.jvm(scala3Version),
      cdclt.jvm(scala3Version),
      lia.jvm(scala3Version),
      vik.jvm(scala3Version),
      smtlib.jvm(scala3Version)
    ),
    ScalaUnidoc / unidoc / target := file("target/unidoc"),
    // The solver, linked to WebAssembly into `docs/_assets/js/vik/`, where the pages of the site load it from.
    docsAssets := Def.uncached { // the linker's report has no hash for sbt's cache; the linker caches by itself
      val linked = (docsPlayground / Compile / fullLinkJS).value.data.publicModules.head
      val _ = (docsPlaygroundJs / Compile / fullLinkJS).value
      val directory = (docsPlayground / Compile / fullLinkJS / scalaJSLinkerOutputDirectory).value
      val javascript = (docsPlaygroundJs / Compile / fullLinkJS / scalaJSLinkerOutputDirectory).value
      val destination = file("docs") / "_assets" / "js"
      IO.delete(destination / "vik")
      IO.delete(destination / "vik-js")
      IO.copyDirectory(directory, destination / "vik")
      IO.copyDirectory(javascript, destination / "vik-js")
      streams.value.log.info(
        s"the solver (${linked.moduleFileName}) is linked into $destination as WebAssembly and as JavaScript"
      )
    },
    ScalaUnidoc / unidoc / scalacOptions ++= Seq(
      "-project",
      "VIK",
      "-siteroot",
      "docs",
      "-Yapi-subdirectory", // the guide at the root of the site, the API documentation under `api/`
      "-project-version",
      version.value,
      "-source-links:github://mbovel/vik/main",
      "-social-links:github::https://github.com/mbovel/vik"
    )
  )
