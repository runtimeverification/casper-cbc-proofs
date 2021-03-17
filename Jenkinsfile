pipeline {
  agent {
    dockerfile {
      label 'docker'
      additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
    }
  }
  options { ansiColor('xterm') }
  environment { COQ_PACKAGE = 'coq-casper-cbc.dev' }
  stages {
    stage('Init title') {
      when { changeRequest() }
      steps { script { currentBuild.displayName = "PR ${env.CHANGE_ID}: ${env.CHANGE_TITLE}" } }
    }
    stage('Prepare and Check') {
      stages {
        stage('Prepare') {
          steps {
            sh '''
              eval $(opam env)
              opam update -y
              opam pin add ${COQ_PACKAGE} . --yes --no-action --kind path
              opam config list
              opam repo list
              opam list
              opam install ${COQ_PACKAGE} --yes -j 6 --deps-only
            '''
          }
        }
        stage('Check') { steps { sh 'eval $(opam env) && opam install ${COQ_PACKAGE} --yes -j 6 --verbose' } }
      }
    }
    stage('Deploy Docs') {
      when { branch 'master' }
      steps {
        sshagent(['2b3d8d6b-0855-4b59-864a-6b3ddf9c9d1a']) {
          sh '''
            eval $(opam env)
            make -j 6
            make coqdoc
            make coq2html
            make -j 6 alectryon
            make -j 6 rvdpd
            export COQ_SHA=$(git rev-parse HEAD)

            git clone 'ssh://github.com/runtimeverification/casper-cbc-proof-docs.git'
            cd casper-cbc-proof-docs
            git checkout -B gh-pages origin/gh-pages

            mkdir docs/${COQ_SHA}
            cd docs
            cp -r ../../docs/coqdoc ${COQ_SHA}
            cp -r ../../docs/coq2html ${COQ_SHA}
            cp -r ../../docs/alectryon ${COQ_SHA}
            ln -sfn ${COQ_SHA} latest
            cd ..

            git add ./
            git commit -m 'gh-pages: update content'
            git push origin gh-pages
          '''
        }
      }
    }
  }
}
