#pragma once

class Application;

class Renderer
{
private:
	Renderer();

public:
	void Update(float r, float g, float b, float a);

	~Renderer();
	friend Application;
};