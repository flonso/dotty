package dotty.tools.sbtplugin

import sbt._
import sbt.Keys._
import java.io._
import java.lang.ProcessBuilder
import scala.collection.mutable

import config.IDEConfig

import com.fasterxml.jackson.databind.ObjectMapper
import scala.collection.mutable.ListBuffer
import DottyPlugin.autoImport._

object DottyIDEPlugin extends AutoPlugin {
  // Adapted from scala-reflect
  private[this] def distinctBy[A, B](xs: Seq[A])(f: A => B): Seq[A] = {
    val buf = new mutable.ListBuffer[A]
    val seen = mutable.Set[B]()
    xs foreach { x =>
      val y = f(x)
      if (!seen(y)) {
        buf += x
        seen += y
      }
    }
    buf.toList
  }

  private def inAllDottyConfigurations[A](key: TaskKey[A], state: State): Task[Seq[A]] = {
    val struct = Project.structure(state)
    val settings = struct.data
    struct.allProjectRefs.flatMap { projRef =>
      val project = Project.getProjectForReference(projRef, struct).get
      project.configurations.flatMap { config =>
        isDotty.in(projRef, config).get(settings) match {
          case Some(true) =>
            key.in(projRef, config).get(settings)
          case _ =>
            None
        }
      }
    }.join
  }

  private val warnWhenStopped = taskKey[Unit]("Warn when compileForIDE was stopped")
  private val ideConfig = taskKey[Option[IDEConfig]]("")

  object autoImport {
    val configureIDE = taskKey[Unit]("Generate IDE config files")
    val compileForIDE = taskKey[Unit]("Compile all projects supported by the IDE")
    val runCode = taskKey[Unit]("Run Visual Studio Code on this project")
  }

  import autoImport._

  override def requires: Plugins = plugins.JvmPlugin
  override def trigger = allRequirements

  override def projectSettings: Seq[Setting[_]] = Seq(
    // Use Def.derive so `ideConfig` is only defined in the configurations where the
    // tasks/settings it depends on are defined.
    Def.derive(ideConfig := {
      if (sources.value.isEmpty) None
      else {
        val id = s"${thisProject.value.id}/${configuration.value.name}"
        val compilerVersion = scalaVersion.value
          .replace("-nonbootstrapped", "") // The language server is only published bootstrapped
        val sourceDirs = unmanagedSourceDirectories.value ++ managedSourceDirectories.value
        val scalacArgs = scalacOptions.value
        val depCp = Attributed.data(dependencyClasspath.value)
        val target = classDirectory.value

        Some(new IDEConfig(
          id,
          compilerVersion,
          sourceDirs.toArray,
          scalacArgs.toArray,
          depCp.toArray,
          target
        ))
      }
    })
  )

  override def buildSettings: Seq[Setting[_]] = Seq(
    // commands ++= Seq(
    //   Command.command("configureIDE")(state => { IDE.writeConfig(state); state })//,
    //   // Command.command("compileForIDE")(state => { IDE.compileForIDE(state); state })
    // ),

    runCode := {
      val exitCode = new ProcessBuilder("code", "--install-extension", "lampepfl.dotty")
        .inheritIO()
        .start()
        .waitFor()
      if (exitCode != 0)
        throw new FeedbackProvidedException {
          override def toString = "Installing the Dotty support for VSCode failed"
        }

      new ProcessBuilder("code", baseDirectory.value.getAbsolutePath)
        .inheritIO()
        .start()
    },

    configureIDE := {
      val log = streams.value.log

      val configs0 = state.flatMap(s =>
        inAllDottyConfigurations(ideConfig, s)
      ).value.flatten
      // Drop configurations who do not define their own sources, but just
      // inherit their sources from some other configuration.
      val configs = distinctBy(configs0)(_.sources.deep)

      if (configs.isEmpty) {
        log.error("No Dotty project detected")
      } else {
        // If different versions of Dotty are used by subprojects, choose the latest one
        // FIXME: use a proper version number Ordering that knows that "0.1.1-M1" < "0.1.1"
        val ideVersion = configs.map(_.scalaVersion).sorted.last
        // Write the version of the Dotty Language Server to use in a file by itself.
        // This could be a field in the JSON config file, but that would require all
        // IDE plugins to parse JSON.
        val pwVersion = new PrintWriter(".dotty-ide-version")
        pwVersion.println(ideVersion)
        pwVersion.close()

        val mapper = new ObjectMapper
        mapper.writerWithDefaultPrettyPrinter()
          .writeValue(new File(".dotty-ide.json"), configs.toArray)
      }
    },

    compileForIDE := {
      val _ = state.flatMap(s =>
        inAllDottyConfigurations(compile, s)
      ).value
    },

    warnWhenStopped := {
      val log = streams.value.log
      log.warn("Incremental compilation was stopped, the IDE will now be inaccurate!")
      log.warn("Run `sbt ~compileForIDE` to keep the IDE working correctly.")
    }
  ) ++
  addCommandAlias("launchIDE", ";configureIDE;runCode;~compileForIDE;warnWhenStopped")
}
