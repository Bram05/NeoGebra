#version 400 core

layout(location = 0) in vec2 pos;
out vec2 v_Pos;

void main()
{
	gl_Position = vec4(pos, 0.0, 1.0);
	v_Pos = pos;
}