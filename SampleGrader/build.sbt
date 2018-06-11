name := "TheoryAssistant"
version := "0.1"
scalaVersion := "2.12.4"
sbtVersion := "1.1.6"
// https://mvnrepository.com/artifact/net.liftweb/lift-json
libraryDependencies += "net.liftweb" %% "lift-json" % "3.1.0-M1"
artifactName := { (sv: ScalaVersion, module: ModuleID, artifact: Artifact) =>
  artifact.name + "." + artifact.extension
}
